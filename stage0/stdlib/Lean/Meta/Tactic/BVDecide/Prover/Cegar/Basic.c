// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Basic public import Lean.Meta.Tactic.BVDecide.TacticContext public import Lean.Cadical.Basic public import Lean.Meta.Tactic.BVDecide.EPR.InstSets
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Internal_Sat_AIG_empty___redArg();
lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_new();
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_array_size(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel;
static const lean_array_object l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1;
static lean_once_cell_t l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2;
static lean_once_cell_t l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1___boxed(lean_object*);
static const lean_array_object l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0 = (const lean_object*)&l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__4_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___boxed(lean_object**);
static lean_once_cell_t l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Lean.Meta.Tactic.BVDecide.CegarM.CounterExample.ofArray"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_CegarCert_solvedWithPreProcessing___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default;
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_unsigned_to_nat(16u);
v___x_11_ = lean_mk_array(v___x_10_, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__0);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default;
return v___x_16_;
}
}
static lean_object* _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_unsigned_to_nat(16u);
v___x_23_ = lean_mk_array(v___x_22_, v___x_21_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1, &l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1_once, _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2, &l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2_once, _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2);
v___x_28_ = ((lean_object*)(l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0));
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3, &l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3_once, _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(lean_object* v_aig_31_){
_start:
{
lean_object* v_decls_32_; lean_object* v___x_33_; uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_decls_32_ = lean_ctor_get(v_aig_31_, 0);
v___x_33_ = lean_array_get_size(v_decls_32_);
v___x_34_ = 0;
v___x_35_ = lean_box(v___x_34_);
v___x_36_ = lean_mk_array(v___x_33_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1___boxed(lean_object* v_aig_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_37_);
lean_dec_ref(v_aig_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(lean_object* v_aig_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0));
v___x_43_ = l___private_Std_Internal_Sat_AIG_CNF_0__Std_Internal_Sat_AIG_toCNF_Cache_init___at___00Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_41_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___boxed(lean_object* v_aig_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v_aig_45_);
lean_dec_ref(v_aig_45_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_52_ = l_Std_Internal_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2);
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_55_ = l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v___x_63_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
lean_ctor_set(v___x_63_, 2, v___x_62_);
lean_ctor_set(v___x_63_, 3, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_65_ = l_Lean_Cadical_Solver_new();
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_67_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3);
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4));
v___x_69_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
v___x_70_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_70_, 0, v___x_66_);
lean_ctor_set(v___x_70_, 1, v___x_67_);
lean_ctor_set(v___x_70_, 2, v___x_68_);
lean_ctor_set(v___x_70_, 3, v___x_69_);
lean_ctor_set(v___x_70_, 4, v___x_65_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_satExpr_77_; lean_object* v_unusedHypotheses_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = lean_st_ref_get(v_a_74_);
v_satExpr_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_satExpr_77_);
lean_dec(v___x_76_);
v_unusedHypotheses_78_ = lean_ctor_get(v_a_73_, 1);
lean_inc_ref(v_unusedHypotheses_78_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v_satExpr_77_);
lean_ctor_set(v___x_79_, 1, v_unusedHypotheses_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg___boxed(lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_85_, v_a_86_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___boxed(lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; uint8_t v_didChange_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_st_ref_get(v_a_117_);
v_didChange_120_ = lean_ctor_get_uint8(v___x_119_, sizeof(void*)*6);
lean_dec(v___x_119_);
v___x_121_ = lean_box(v_didChange_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg___boxed(lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(v_a_123_);
lean_dec(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_141_; uint8_t v_didChange_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = lean_st_ref_get(v_a_127_);
v_didChange_142_ = lean_ctor_get_uint8(v___x_141_, sizeof(void*)*6);
lean_dec(v___x_141_);
v___x_143_ = lean_box(v_didChange_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___boxed(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(uint8_t v_v_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_satExpr_165_; lean_object* v_hypQueue_166_; lean_object* v_usedHyps_167_; lean_object* v_theoryState_168_; lean_object* v_solverTimeBudgetMs_169_; lean_object* v_roundBudget_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v___x_164_ = lean_st_ref_take(v_a_162_);
v_satExpr_165_ = lean_ctor_get(v___x_164_, 0);
v_hypQueue_166_ = lean_ctor_get(v___x_164_, 1);
v_usedHyps_167_ = lean_ctor_get(v___x_164_, 2);
v_theoryState_168_ = lean_ctor_get(v___x_164_, 3);
v_solverTimeBudgetMs_169_ = lean_ctor_get(v___x_164_, 4);
v_roundBudget_170_ = lean_ctor_get(v___x_164_, 5);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v___x_164_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_roundBudget_170_);
lean_inc(v_solverTimeBudgetMs_169_);
lean_inc(v_theoryState_168_);
lean_inc(v_usedHyps_167_);
lean_inc(v_hypQueue_166_);
lean_inc(v_satExpr_165_);
lean_dec(v___x_164_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_box(0);
if (v_isShared_173_ == 0)
{
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_satExpr_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_hypQueue_166_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_usedHyps_167_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_theoryState_168_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_solverTimeBudgetMs_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 5, v_roundBudget_170_);
v___x_176_ = v_reuseFailAlloc_179_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*6, v_v_161_);
v___x_177_ = lean_st_ref_put(v_a_162_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_174_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg___boxed(lean_object* v_v_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
uint8_t v_v_boxed_184_; lean_object* v_res_185_; 
v_v_boxed_184_ = lean_unbox(v_v_181_);
v_res_185_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(v_v_boxed_184_, v_a_182_);
lean_dec(v_a_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(uint8_t v_v_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; lean_object* v_satExpr_203_; lean_object* v_hypQueue_204_; lean_object* v_usedHyps_205_; lean_object* v_theoryState_206_; lean_object* v_solverTimeBudgetMs_207_; lean_object* v_roundBudget_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v___x_202_ = lean_st_ref_take(v_a_188_);
v_satExpr_203_ = lean_ctor_get(v___x_202_, 0);
v_hypQueue_204_ = lean_ctor_get(v___x_202_, 1);
v_usedHyps_205_ = lean_ctor_get(v___x_202_, 2);
v_theoryState_206_ = lean_ctor_get(v___x_202_, 3);
v_solverTimeBudgetMs_207_ = lean_ctor_get(v___x_202_, 4);
v_roundBudget_208_ = lean_ctor_get(v___x_202_, 5);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v___x_202_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_roundBudget_208_);
lean_inc(v_solverTimeBudgetMs_207_);
lean_inc(v_theoryState_206_);
lean_inc(v_usedHyps_205_);
lean_inc(v_hypQueue_204_);
lean_inc(v_satExpr_203_);
lean_dec(v___x_202_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_box(0);
if (v_isShared_211_ == 0)
{
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_satExpr_203_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_hypQueue_204_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_usedHyps_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_theoryState_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_solverTimeBudgetMs_207_);
lean_ctor_set(v_reuseFailAlloc_217_, 5, v_roundBudget_208_);
v___x_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*6, v_v_186_);
v___x_215_ = lean_st_ref_put(v_a_188_, v___x_214_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_212_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___boxed(lean_object* v_v_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
uint8_t v_v_boxed_235_; lean_object* v_res_236_; 
v_v_boxed_235_ = lean_unbox(v_v_219_);
v_res_236_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(v_v_boxed_235_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_theoryState_240_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_get(v_a_237_);
v_theoryState_240_ = lean_ctor_get(v___x_239_, 3);
lean_inc_ref(v_theoryState_240_);
lean_dec(v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v_theoryState_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg___boxed(lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(v_a_242_);
lean_dec(v_a_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; lean_object* v_theoryState_261_; lean_object* v___x_262_; 
v___x_260_ = lean_st_ref_get(v_a_246_);
v_theoryState_261_ = lean_ctor_get(v___x_260_, 3);
lean_inc_ref(v_theoryState_261_);
lean_dec(v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_theoryState_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___boxed(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(lean_object* v_f_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_satExpr_283_; lean_object* v_hypQueue_284_; lean_object* v_usedHyps_285_; uint8_t v_didChange_286_; lean_object* v_theoryState_287_; lean_object* v_solverTimeBudgetMs_288_; lean_object* v_roundBudget_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_300_; 
v___x_282_ = lean_st_ref_take(v_a_280_);
v_satExpr_283_ = lean_ctor_get(v___x_282_, 0);
v_hypQueue_284_ = lean_ctor_get(v___x_282_, 1);
v_usedHyps_285_ = lean_ctor_get(v___x_282_, 2);
v_didChange_286_ = lean_ctor_get_uint8(v___x_282_, sizeof(void*)*6);
v_theoryState_287_ = lean_ctor_get(v___x_282_, 3);
v_solverTimeBudgetMs_288_ = lean_ctor_get(v___x_282_, 4);
v_roundBudget_289_ = lean_ctor_get(v___x_282_, 5);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_300_ == 0)
{
v___x_291_ = v___x_282_;
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_roundBudget_289_);
lean_inc(v_solverTimeBudgetMs_288_);
lean_inc(v_theoryState_287_);
lean_inc(v_usedHyps_285_);
lean_inc(v_hypQueue_284_);
lean_inc(v_satExpr_283_);
lean_dec(v___x_282_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_300_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_1(v_f_279_, v_theoryState_287_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 3, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_satExpr_283_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_hypQueue_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_usedHyps_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_solverTimeBudgetMs_288_);
lean_ctor_set(v_reuseFailAlloc_299_, 5, v_roundBudget_289_);
lean_ctor_set_uint8(v_reuseFailAlloc_299_, sizeof(void*)*6, v_didChange_286_);
v___x_296_ = v_reuseFailAlloc_299_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_st_ref_put(v_a_280_, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_293_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg___boxed(lean_object* v_f_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(v_f_301_, v_a_302_);
lean_dec(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_satExpr_322_; lean_object* v_hypQueue_323_; lean_object* v_usedHyps_324_; uint8_t v_didChange_325_; lean_object* v_theoryState_326_; lean_object* v_solverTimeBudgetMs_327_; lean_object* v_roundBudget_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
v___x_321_ = lean_st_ref_take(v_a_307_);
v_satExpr_322_ = lean_ctor_get(v___x_321_, 0);
v_hypQueue_323_ = lean_ctor_get(v___x_321_, 1);
v_usedHyps_324_ = lean_ctor_get(v___x_321_, 2);
v_didChange_325_ = lean_ctor_get_uint8(v___x_321_, sizeof(void*)*6);
v_theoryState_326_ = lean_ctor_get(v___x_321_, 3);
v_solverTimeBudgetMs_327_ = lean_ctor_get(v___x_321_, 4);
v_roundBudget_328_ = lean_ctor_get(v___x_321_, 5);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_339_ == 0)
{
v___x_330_ = v___x_321_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_roundBudget_328_);
lean_inc(v_solverTimeBudgetMs_327_);
lean_inc(v_theoryState_326_);
lean_inc(v_usedHyps_324_);
lean_inc(v_hypQueue_323_);
lean_inc(v_satExpr_322_);
lean_dec(v___x_321_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_1(v_f_305_, v_theoryState_326_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 3, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_satExpr_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_hypQueue_323_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_usedHyps_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_solverTimeBudgetMs_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_roundBudget_328_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*6, v_didChange_325_);
v___x_335_ = v_reuseFailAlloc_338_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_st_ref_put(v_a_307_, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_332_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___boxed(lean_object* v_f_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(v_f_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_Internal_Sat_AIG_empty___redArg();
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_359_ = l_Std_Internal_Sat_AIG_toCNF_State_empty___redArg(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1);
v___x_361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_362_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___x_361_);
lean_ctor_set(v___x_363_, 2, v___x_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; lean_object* v_theoryState_367_; lean_object* v_satExpr_368_; lean_object* v_hypQueue_369_; lean_object* v_usedHyps_370_; uint8_t v_didChange_371_; lean_object* v_solverTimeBudgetMs_372_; lean_object* v_roundBudget_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_398_; 
v___x_366_ = lean_st_ref_take(v_a_364_);
v_theoryState_367_ = lean_ctor_get(v___x_366_, 3);
v_satExpr_368_ = lean_ctor_get(v___x_366_, 0);
v_hypQueue_369_ = lean_ctor_get(v___x_366_, 1);
v_usedHyps_370_ = lean_ctor_get(v___x_366_, 2);
v_didChange_371_ = lean_ctor_get_uint8(v___x_366_, sizeof(void*)*6);
v_solverTimeBudgetMs_372_ = lean_ctor_get(v___x_366_, 4);
v_roundBudget_373_ = lean_ctor_get(v___x_366_, 5);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_398_ == 0)
{
v___x_375_ = v___x_366_;
v_isShared_376_ = v_isSharedCheck_398_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_roundBudget_373_);
lean_inc(v_solverTimeBudgetMs_372_);
lean_inc(v_theoryState_367_);
lean_inc(v_usedHyps_370_);
lean_inc(v_hypQueue_369_);
lean_inc(v_satExpr_368_);
lean_dec(v___x_366_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_398_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_eprState_377_; lean_object* v_satSolver_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_eprState_377_ = lean_ctor_get(v_theoryState_367_, 2);
v_satSolver_378_ = lean_ctor_get(v_theoryState_367_, 4);
v_isSharedCheck_394_ = !lean_is_exclusive(v_theoryState_367_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_395_ = lean_ctor_get(v_theoryState_367_, 3);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_theoryState_367_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_theoryState_367_, 0);
lean_dec(v_unused_397_);
v___x_380_ = v_theoryState_367_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_satSolver_378_);
lean_inc(v_eprState_377_);
lean_dec(v_theoryState_367_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_382_ = lean_box(0);
v___x_383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_384_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
v___x_385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 3, v___x_385_);
lean_ctor_set(v___x_380_, 1, v___x_384_);
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_387_ = v___x_380_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_eprState_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_satSolver_378_);
v___x_387_ = v_reuseFailAlloc_393_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 3, v___x_387_);
v___x_389_ = v___x_375_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_satExpr_368_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_hypQueue_369_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_usedHyps_370_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_solverTimeBudgetMs_372_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_roundBudget_373_);
lean_ctor_set_uint8(v_reuseFailAlloc_392_, sizeof(void*)*6, v_didChange_371_);
v___x_389_ = v_reuseFailAlloc_392_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_st_ref_put(v_a_364_, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_382_);
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___boxed(lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(v_a_399_);
lean_dec(v_a_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; lean_object* v_satExpr_418_; lean_object* v_hypQueue_419_; lean_object* v_usedHyps_420_; uint8_t v_didChange_421_; lean_object* v_theoryState_422_; lean_object* v_solverTimeBudgetMs_423_; lean_object* v_roundBudget_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_449_; 
v___x_417_ = lean_st_ref_take(v_a_403_);
v_satExpr_418_ = lean_ctor_get(v___x_417_, 0);
v_hypQueue_419_ = lean_ctor_get(v___x_417_, 1);
v_usedHyps_420_ = lean_ctor_get(v___x_417_, 2);
v_didChange_421_ = lean_ctor_get_uint8(v___x_417_, sizeof(void*)*6);
v_theoryState_422_ = lean_ctor_get(v___x_417_, 3);
v_solverTimeBudgetMs_423_ = lean_ctor_get(v___x_417_, 4);
v_roundBudget_424_ = lean_ctor_get(v___x_417_, 5);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_449_ == 0)
{
v___x_426_ = v___x_417_;
v_isShared_427_ = v_isSharedCheck_449_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_roundBudget_424_);
lean_inc(v_solverTimeBudgetMs_423_);
lean_inc(v_theoryState_422_);
lean_inc(v_usedHyps_420_);
lean_inc(v_hypQueue_419_);
lean_inc(v_satExpr_418_);
lean_dec(v___x_417_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_449_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_eprState_428_; lean_object* v_satSolver_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_445_; 
v_eprState_428_ = lean_ctor_get(v_theoryState_422_, 2);
v_satSolver_429_ = lean_ctor_get(v_theoryState_422_, 4);
v_isSharedCheck_445_ = !lean_is_exclusive(v_theoryState_422_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_446_ = lean_ctor_get(v_theoryState_422_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_theoryState_422_, 1);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_theoryState_422_, 0);
lean_dec(v_unused_448_);
v___x_431_ = v_theoryState_422_;
v_isShared_432_ = v_isSharedCheck_445_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_satSolver_429_);
lean_inc(v_eprState_428_);
lean_dec(v_theoryState_422_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_445_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_435_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
v___x_436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 3, v___x_436_);
lean_ctor_set(v___x_431_, 1, v___x_435_);
lean_ctor_set(v___x_431_, 0, v___x_434_);
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_eprState_428_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_satSolver_429_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 3, v___x_438_);
v___x_440_ = v___x_426_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_satExpr_418_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_hypQueue_419_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_usedHyps_420_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_solverTimeBudgetMs_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_roundBudget_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*6, v_didChange_421_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_st_ref_put(v_a_403_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_433_);
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___boxed(lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(lean_object* v_hyp_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_469_; lean_object* v_satExpr_470_; lean_object* v_hypQueue_471_; lean_object* v_usedHyps_472_; uint8_t v_didChange_473_; lean_object* v_theoryState_474_; lean_object* v_solverTimeBudgetMs_475_; lean_object* v_roundBudget_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_487_; 
v___x_469_ = lean_st_ref_take(v_a_467_);
v_satExpr_470_ = lean_ctor_get(v___x_469_, 0);
v_hypQueue_471_ = lean_ctor_get(v___x_469_, 1);
v_usedHyps_472_ = lean_ctor_get(v___x_469_, 2);
v_didChange_473_ = lean_ctor_get_uint8(v___x_469_, sizeof(void*)*6);
v_theoryState_474_ = lean_ctor_get(v___x_469_, 3);
v_solverTimeBudgetMs_475_ = lean_ctor_get(v___x_469_, 4);
v_roundBudget_476_ = lean_ctor_get(v___x_469_, 5);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_487_ == 0)
{
v___x_478_ = v___x_469_;
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_roundBudget_476_);
lean_inc(v_solverTimeBudgetMs_475_);
lean_inc(v_theoryState_474_);
lean_inc(v_usedHyps_472_);
lean_inc(v_hypQueue_471_);
lean_inc(v_satExpr_470_);
lean_dec(v___x_469_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_array_push(v_hypQueue_471_, v_hyp_466_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_satExpr_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_usedHyps_472_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_theoryState_474_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_solverTimeBudgetMs_475_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_roundBudget_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*6, v_didChange_473_);
v___x_483_ = v_reuseFailAlloc_486_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_st_ref_put(v_a_467_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_480_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg___boxed(lean_object* v_hyp_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(v_hyp_488_, v_a_489_);
lean_dec(v_a_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(lean_object* v_hyp_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v_satExpr_509_; lean_object* v_hypQueue_510_; lean_object* v_usedHyps_511_; uint8_t v_didChange_512_; lean_object* v_theoryState_513_; lean_object* v_solverTimeBudgetMs_514_; lean_object* v_roundBudget_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_526_; 
v___x_508_ = lean_st_ref_take(v_a_494_);
v_satExpr_509_ = lean_ctor_get(v___x_508_, 0);
v_hypQueue_510_ = lean_ctor_get(v___x_508_, 1);
v_usedHyps_511_ = lean_ctor_get(v___x_508_, 2);
v_didChange_512_ = lean_ctor_get_uint8(v___x_508_, sizeof(void*)*6);
v_theoryState_513_ = lean_ctor_get(v___x_508_, 3);
v_solverTimeBudgetMs_514_ = lean_ctor_get(v___x_508_, 4);
v_roundBudget_515_ = lean_ctor_get(v___x_508_, 5);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_526_ == 0)
{
v___x_517_ = v___x_508_;
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_roundBudget_515_);
lean_inc(v_solverTimeBudgetMs_514_);
lean_inc(v_theoryState_513_);
lean_inc(v_usedHyps_511_);
lean_inc(v_hypQueue_510_);
lean_inc(v_satExpr_509_);
lean_dec(v___x_508_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_array_push(v_hypQueue_510_, v_hyp_492_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___x_520_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_satExpr_509_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_usedHyps_511_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_theoryState_513_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_solverTimeBudgetMs_514_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_roundBudget_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_525_, sizeof(void*)*6, v_didChange_512_);
v___x_522_ = v_reuseFailAlloc_525_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_st_ref_put(v_a_494_, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_519_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___boxed(lean_object* v_hyp_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(v_hyp_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(lean_object* v_a_544_){
_start:
{
lean_object* v___x_546_; lean_object* v_usedHyps_547_; lean_object* v___x_548_; 
v___x_546_ = lean_st_ref_get(v_a_544_);
v_usedHyps_547_ = lean_ctor_get(v___x_546_, 2);
lean_inc_ref(v_usedHyps_547_);
lean_dec(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_usedHyps_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg___boxed(lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(v_a_549_);
lean_dec(v_a_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_usedHyps_568_; lean_object* v___x_569_; 
v___x_567_ = lean_st_ref_get(v_a_553_);
v_usedHyps_568_ = lean_ctor_get(v___x_567_, 2);
lean_inc_ref(v_usedHyps_568_);
lean_dec(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_usedHyps_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___boxed(lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; lean_object* v_satExpr_591_; lean_object* v_hypQueue_592_; lean_object* v_usedHyps_593_; uint8_t v_didChange_594_; lean_object* v_theoryState_595_; lean_object* v_solverTimeBudgetMs_596_; lean_object* v_roundBudget_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_608_; 
v___x_590_ = lean_st_ref_take(v_a_588_);
v_satExpr_591_ = lean_ctor_get(v___x_590_, 0);
v_hypQueue_592_ = lean_ctor_get(v___x_590_, 1);
v_usedHyps_593_ = lean_ctor_get(v___x_590_, 2);
v_didChange_594_ = lean_ctor_get_uint8(v___x_590_, sizeof(void*)*6);
v_theoryState_595_ = lean_ctor_get(v___x_590_, 3);
v_solverTimeBudgetMs_596_ = lean_ctor_get(v___x_590_, 4);
v_roundBudget_597_ = lean_ctor_get(v___x_590_, 5);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_608_ == 0)
{
v___x_599_ = v___x_590_;
v_isShared_600_ = v_isSharedCheck_608_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_roundBudget_597_);
lean_inc(v_solverTimeBudgetMs_596_);
lean_inc(v_theoryState_595_);
lean_inc(v_usedHyps_593_);
lean_inc(v_hypQueue_592_);
lean_inc(v_satExpr_591_);
lean_dec(v___x_590_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_608_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_601_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_602_ = l_Array_append___redArg(v_usedHyps_593_, v_hypQueue_592_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 2, v___x_602_);
lean_ctor_set(v___x_599_, 1, v___x_601_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_satExpr_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_theoryState_595_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_solverTimeBudgetMs_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_roundBudget_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*6, v_didChange_594_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_st_ref_put(v_a_588_, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v_hypQueue_592_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___boxed(lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(v_a_609_);
lean_dec(v_a_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_satExpr_628_; lean_object* v_hypQueue_629_; lean_object* v_usedHyps_630_; uint8_t v_didChange_631_; lean_object* v_theoryState_632_; lean_object* v_solverTimeBudgetMs_633_; lean_object* v_roundBudget_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v___x_627_ = lean_st_ref_take(v_a_613_);
v_satExpr_628_ = lean_ctor_get(v___x_627_, 0);
v_hypQueue_629_ = lean_ctor_get(v___x_627_, 1);
v_usedHyps_630_ = lean_ctor_get(v___x_627_, 2);
v_didChange_631_ = lean_ctor_get_uint8(v___x_627_, sizeof(void*)*6);
v_theoryState_632_ = lean_ctor_get(v___x_627_, 3);
v_solverTimeBudgetMs_633_ = lean_ctor_get(v___x_627_, 4);
v_roundBudget_634_ = lean_ctor_get(v___x_627_, 5);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_645_ == 0)
{
v___x_636_ = v___x_627_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_roundBudget_634_);
lean_inc(v_solverTimeBudgetMs_633_);
lean_inc(v_theoryState_632_);
lean_inc(v_usedHyps_630_);
lean_inc(v_hypQueue_629_);
lean_inc(v_satExpr_628_);
lean_dec(v___x_627_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_639_ = l_Array_append___redArg(v_usedHyps_630_, v_hypQueue_629_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_639_);
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_satExpr_628_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_theoryState_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_solverTimeBudgetMs_633_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v_roundBudget_634_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*6, v_didChange_631_);
v___x_641_ = v_reuseFailAlloc_644_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_st_ref_put(v_a_613_, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_hypQueue_629_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___boxed(lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(lean_object* v_a_662_){
_start:
{
lean_object* v_tacticContext_664_; lean_object* v___x_665_; 
v_tacticContext_664_ = lean_ctor_get(v_a_662_, 2);
lean_inc_ref(v_tacticContext_664_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v_tacticContext_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg___boxed(lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(v_a_666_);
lean_dec_ref(v_a_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_tacticContext_684_; lean_object* v___x_685_; 
v_tacticContext_684_ = lean_ctor_get(v_a_669_, 2);
lean_inc_ref(v_tacticContext_684_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_tacticContext_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___boxed(lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(lean_object* v_a_702_){
_start:
{
lean_object* v_tacticContext_704_; lean_object* v_config_705_; uint8_t v_uf_706_; 
v_tacticContext_704_ = lean_ctor_get(v_a_702_, 2);
v_config_705_ = lean_ctor_get(v_tacticContext_704_, 5);
v_uf_706_ = lean_ctor_get_uint8(v_config_705_, sizeof(void*)*3 + 11);
if (v_uf_706_ == 0)
{
uint8_t v_epr_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_epr_707_ = lean_ctor_get_uint8(v_config_705_, sizeof(void*)*3 + 12);
v___x_708_ = lean_box(v_epr_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_box(v_uf_706_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg___boxed(lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(v_a_712_);
lean_dec_ref(v_a_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_tacticContext_730_; lean_object* v_config_731_; uint8_t v_uf_732_; 
v_tacticContext_730_ = lean_ctor_get(v_a_715_, 2);
v_config_731_ = lean_ctor_get(v_tacticContext_730_, 5);
v_uf_732_ = lean_ctor_get_uint8(v_config_731_, sizeof(void*)*3 + 11);
if (v_uf_732_ == 0)
{
uint8_t v_epr_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_epr_733_ = lean_ctor_get_uint8(v_config_731_, sizeof(void*)*3 + 12);
v___x_734_ = lean_box(v_epr_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_box(v_uf_732_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___boxed(lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(lean_object* v_ms_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; lean_object* v_satExpr_758_; lean_object* v_hypQueue_759_; lean_object* v_usedHyps_760_; uint8_t v_didChange_761_; lean_object* v_theoryState_762_; lean_object* v_solverTimeBudgetMs_763_; lean_object* v_roundBudget_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_775_; 
v___x_757_ = lean_st_ref_take(v_a_755_);
v_satExpr_758_ = lean_ctor_get(v___x_757_, 0);
v_hypQueue_759_ = lean_ctor_get(v___x_757_, 1);
v_usedHyps_760_ = lean_ctor_get(v___x_757_, 2);
v_didChange_761_ = lean_ctor_get_uint8(v___x_757_, sizeof(void*)*6);
v_theoryState_762_ = lean_ctor_get(v___x_757_, 3);
v_solverTimeBudgetMs_763_ = lean_ctor_get(v___x_757_, 4);
v_roundBudget_764_ = lean_ctor_get(v___x_757_, 5);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_775_ == 0)
{
v___x_766_ = v___x_757_;
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_roundBudget_764_);
lean_inc(v_solverTimeBudgetMs_763_);
lean_inc(v_theoryState_762_);
lean_inc(v_usedHyps_760_);
lean_inc(v_hypQueue_759_);
lean_inc(v_satExpr_758_);
lean_dec(v___x_757_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_nat_sub(v_solverTimeBudgetMs_763_, v_ms_754_);
lean_dec(v_solverTimeBudgetMs_763_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 4, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_satExpr_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_hypQueue_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_usedHyps_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_theoryState_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_roundBudget_764_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*6, v_didChange_761_);
v___x_771_ = v_reuseFailAlloc_774_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_st_ref_put(v_a_755_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_768_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg___boxed(lean_object* v_ms_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(v_ms_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec(v_ms_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(lean_object* v_ms_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_satExpr_797_; lean_object* v_hypQueue_798_; lean_object* v_usedHyps_799_; uint8_t v_didChange_800_; lean_object* v_theoryState_801_; lean_object* v_solverTimeBudgetMs_802_; lean_object* v_roundBudget_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_814_; 
v___x_796_ = lean_st_ref_take(v_a_782_);
v_satExpr_797_ = lean_ctor_get(v___x_796_, 0);
v_hypQueue_798_ = lean_ctor_get(v___x_796_, 1);
v_usedHyps_799_ = lean_ctor_get(v___x_796_, 2);
v_didChange_800_ = lean_ctor_get_uint8(v___x_796_, sizeof(void*)*6);
v_theoryState_801_ = lean_ctor_get(v___x_796_, 3);
v_solverTimeBudgetMs_802_ = lean_ctor_get(v___x_796_, 4);
v_roundBudget_803_ = lean_ctor_get(v___x_796_, 5);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_814_ == 0)
{
v___x_805_ = v___x_796_;
v_isShared_806_ = v_isSharedCheck_814_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_roundBudget_803_);
lean_inc(v_solverTimeBudgetMs_802_);
lean_inc(v_theoryState_801_);
lean_inc(v_usedHyps_799_);
lean_inc(v_hypQueue_798_);
lean_inc(v_satExpr_797_);
lean_dec(v___x_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_814_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_807_ = lean_box(0);
v___x_808_ = lean_nat_sub(v_solverTimeBudgetMs_802_, v_ms_780_);
lean_dec(v_solverTimeBudgetMs_802_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 4, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_satExpr_797_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_hypQueue_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_usedHyps_799_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_theoryState_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_813_, 5, v_roundBudget_803_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*6, v_didChange_800_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_st_ref_put(v_a_782_, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_807_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___boxed(lean_object* v_ms_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(v_ms_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_ms_815_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; lean_object* v_solverTimeBudgetMs_835_; lean_object* v___x_836_; 
v___x_834_ = lean_st_ref_get(v_a_832_);
v_solverTimeBudgetMs_835_ = lean_ctor_get(v___x_834_, 4);
lean_inc(v_solverTimeBudgetMs_835_);
lean_dec(v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_solverTimeBudgetMs_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg___boxed(lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(v_a_837_);
lean_dec(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; lean_object* v_solverTimeBudgetMs_856_; lean_object* v___x_857_; 
v___x_855_ = lean_st_ref_get(v_a_841_);
v_solverTimeBudgetMs_856_ = lean_ctor_get(v___x_855_, 4);
lean_inc(v_solverTimeBudgetMs_856_);
lean_dec(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v_solverTimeBudgetMs_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___boxed(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; lean_object* v_satExpr_877_; lean_object* v_hypQueue_878_; lean_object* v_usedHyps_879_; uint8_t v_didChange_880_; lean_object* v_theoryState_881_; lean_object* v_solverTimeBudgetMs_882_; lean_object* v_roundBudget_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_895_; 
v___x_876_ = lean_st_ref_take(v_a_874_);
v_satExpr_877_ = lean_ctor_get(v___x_876_, 0);
v_hypQueue_878_ = lean_ctor_get(v___x_876_, 1);
v_usedHyps_879_ = lean_ctor_get(v___x_876_, 2);
v_didChange_880_ = lean_ctor_get_uint8(v___x_876_, sizeof(void*)*6);
v_theoryState_881_ = lean_ctor_get(v___x_876_, 3);
v_solverTimeBudgetMs_882_ = lean_ctor_get(v___x_876_, 4);
v_roundBudget_883_ = lean_ctor_get(v___x_876_, 5);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_885_ = v___x_876_;
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_roundBudget_883_);
lean_inc(v_solverTimeBudgetMs_882_);
lean_inc(v_theoryState_881_);
lean_inc(v_usedHyps_879_);
lean_inc(v_hypQueue_878_);
lean_inc(v_satExpr_877_);
lean_dec(v___x_876_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_895_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_887_ = lean_box(0);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_sub(v_roundBudget_883_, v___x_888_);
lean_dec(v_roundBudget_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 5, v___x_889_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_satExpr_877_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_hypQueue_878_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_usedHyps_879_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_theoryState_881_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_solverTimeBudgetMs_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 5, v___x_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*6, v_didChange_880_);
v___x_891_ = v_reuseFailAlloc_894_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_st_ref_put(v_a_874_, v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_887_);
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg___boxed(lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(v_a_896_);
lean_dec(v_a_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_satExpr_915_; lean_object* v_hypQueue_916_; lean_object* v_usedHyps_917_; uint8_t v_didChange_918_; lean_object* v_theoryState_919_; lean_object* v_solverTimeBudgetMs_920_; lean_object* v_roundBudget_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_933_; 
v___x_914_ = lean_st_ref_take(v_a_900_);
v_satExpr_915_ = lean_ctor_get(v___x_914_, 0);
v_hypQueue_916_ = lean_ctor_get(v___x_914_, 1);
v_usedHyps_917_ = lean_ctor_get(v___x_914_, 2);
v_didChange_918_ = lean_ctor_get_uint8(v___x_914_, sizeof(void*)*6);
v_theoryState_919_ = lean_ctor_get(v___x_914_, 3);
v_solverTimeBudgetMs_920_ = lean_ctor_get(v___x_914_, 4);
v_roundBudget_921_ = lean_ctor_get(v___x_914_, 5);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_933_ == 0)
{
v___x_923_ = v___x_914_;
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_roundBudget_921_);
lean_inc(v_solverTimeBudgetMs_920_);
lean_inc(v_theoryState_919_);
lean_inc(v_usedHyps_917_);
lean_inc(v_hypQueue_916_);
lean_inc(v_satExpr_915_);
lean_dec(v___x_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_sub(v_roundBudget_921_, v___x_926_);
lean_dec(v_roundBudget_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 5, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_satExpr_915_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_hypQueue_916_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_usedHyps_917_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_theoryState_919_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_solverTimeBudgetMs_920_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v___x_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_932_, sizeof(void*)*6, v_didChange_918_);
v___x_929_ = v_reuseFailAlloc_932_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_st_ref_put(v_a_900_, v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_925_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___boxed(lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_roundBudget_953_; lean_object* v___x_954_; 
v___x_952_ = lean_st_ref_get(v_a_950_);
v_roundBudget_953_ = lean_ctor_get(v___x_952_, 5);
lean_inc(v_roundBudget_953_);
lean_dec(v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v_roundBudget_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg___boxed(lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(v_a_955_);
lean_dec(v_a_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_roundBudget_974_; lean_object* v___x_975_; 
v___x_973_ = lean_st_ref_get(v_a_959_);
v_roundBudget_974_ = lean_ctor_get(v___x_973_, 5);
lean_inc(v_roundBudget_974_);
lean_dec(v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_roundBudget_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___boxed(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_theoryState_995_; lean_object* v_satExpr_996_; lean_object* v_hypQueue_997_; lean_object* v_usedHyps_998_; uint8_t v_didChange_999_; lean_object* v_solverTimeBudgetMs_1000_; lean_object* v_roundBudget_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1023_; 
v___x_994_ = lean_st_ref_take(v_a_992_);
v_theoryState_995_ = lean_ctor_get(v___x_994_, 3);
v_satExpr_996_ = lean_ctor_get(v___x_994_, 0);
v_hypQueue_997_ = lean_ctor_get(v___x_994_, 1);
v_usedHyps_998_ = lean_ctor_get(v___x_994_, 2);
v_didChange_999_ = lean_ctor_get_uint8(v___x_994_, sizeof(void*)*6);
v_solverTimeBudgetMs_1000_ = lean_ctor_get(v___x_994_, 4);
v_roundBudget_1001_ = lean_ctor_get(v___x_994_, 5);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1003_ = v___x_994_;
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_roundBudget_1001_);
lean_inc(v_solverTimeBudgetMs_1000_);
lean_inc(v_theoryState_995_);
lean_inc(v_usedHyps_998_);
lean_inc(v_hypQueue_997_);
lean_inc(v_satExpr_996_);
lean_dec(v___x_994_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_funState_1005_; lean_object* v_bitvecState_1006_; lean_object* v_eprState_1007_; lean_object* v_preprocessCaches_1008_; lean_object* v_satSolver_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1022_; 
v_funState_1005_ = lean_ctor_get(v_theoryState_995_, 0);
v_bitvecState_1006_ = lean_ctor_get(v_theoryState_995_, 1);
v_eprState_1007_ = lean_ctor_get(v_theoryState_995_, 2);
v_preprocessCaches_1008_ = lean_ctor_get(v_theoryState_995_, 3);
v_satSolver_1009_ = lean_ctor_get(v_theoryState_995_, 4);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_theoryState_995_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1011_ = v_theoryState_995_;
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_satSolver_1009_);
lean_inc(v_preprocessCaches_1008_);
lean_inc(v_eprState_1007_);
lean_inc(v_bitvecState_1006_);
lean_inc(v_funState_1005_);
lean_dec(v_theoryState_995_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 3, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_funState_1005_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_bitvecState_1006_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_eprState_1007_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_satSolver_1009_);
v___x_1015_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 3, v___x_1015_);
v___x_1017_ = v___x_1003_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_satExpr_996_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_hypQueue_997_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_usedHyps_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_solverTimeBudgetMs_1000_);
lean_ctor_set(v_reuseFailAlloc_1020_, 5, v_roundBudget_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1020_, sizeof(void*)*6, v_didChange_999_);
v___x_1017_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_st_ref_put(v_a_992_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_preprocessCaches_1008_);
return v___x_1019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg___boxed(lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(v_a_1024_);
lean_dec(v_a_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_theoryState_1043_; lean_object* v_satExpr_1044_; lean_object* v_hypQueue_1045_; lean_object* v_usedHyps_1046_; uint8_t v_didChange_1047_; lean_object* v_solverTimeBudgetMs_1048_; lean_object* v_roundBudget_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1071_; 
v___x_1042_ = lean_st_ref_take(v_a_1028_);
v_theoryState_1043_ = lean_ctor_get(v___x_1042_, 3);
v_satExpr_1044_ = lean_ctor_get(v___x_1042_, 0);
v_hypQueue_1045_ = lean_ctor_get(v___x_1042_, 1);
v_usedHyps_1046_ = lean_ctor_get(v___x_1042_, 2);
v_didChange_1047_ = lean_ctor_get_uint8(v___x_1042_, sizeof(void*)*6);
v_solverTimeBudgetMs_1048_ = lean_ctor_get(v___x_1042_, 4);
v_roundBudget_1049_ = lean_ctor_get(v___x_1042_, 5);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1051_ = v___x_1042_;
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_roundBudget_1049_);
lean_inc(v_solverTimeBudgetMs_1048_);
lean_inc(v_theoryState_1043_);
lean_inc(v_usedHyps_1046_);
lean_inc(v_hypQueue_1045_);
lean_inc(v_satExpr_1044_);
lean_dec(v___x_1042_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_funState_1053_; lean_object* v_bitvecState_1054_; lean_object* v_eprState_1055_; lean_object* v_preprocessCaches_1056_; lean_object* v_satSolver_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1070_; 
v_funState_1053_ = lean_ctor_get(v_theoryState_1043_, 0);
v_bitvecState_1054_ = lean_ctor_get(v_theoryState_1043_, 1);
v_eprState_1055_ = lean_ctor_get(v_theoryState_1043_, 2);
v_preprocessCaches_1056_ = lean_ctor_get(v_theoryState_1043_, 3);
v_satSolver_1057_ = lean_ctor_get(v_theoryState_1043_, 4);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_theoryState_1043_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1059_ = v_theoryState_1043_;
v_isShared_1060_ = v_isSharedCheck_1070_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_satSolver_1057_);
lean_inc(v_preprocessCaches_1056_);
lean_inc(v_eprState_1055_);
lean_inc(v_bitvecState_1054_);
lean_inc(v_funState_1053_);
lean_dec(v_theoryState_1043_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1070_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 3, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_funState_1053_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_bitvecState_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_eprState_1055_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_satSolver_1057_);
v___x_1063_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 3, v___x_1063_);
v___x_1065_ = v___x_1051_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_satExpr_1044_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_hypQueue_1045_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_usedHyps_1046_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_solverTimeBudgetMs_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 5, v_roundBudget_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1068_, sizeof(void*)*6, v_didChange_1047_);
v___x_1065_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_st_ref_put(v_a_1028_, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_preprocessCaches_1056_);
return v___x_1067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___boxed(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(lean_object* v_caches_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v_theoryState_1092_; lean_object* v_satExpr_1093_; lean_object* v_hypQueue_1094_; lean_object* v_usedHyps_1095_; uint8_t v_didChange_1096_; lean_object* v_solverTimeBudgetMs_1097_; lean_object* v_roundBudget_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1120_; 
v___x_1091_ = lean_st_ref_take(v_a_1089_);
v_theoryState_1092_ = lean_ctor_get(v___x_1091_, 3);
v_satExpr_1093_ = lean_ctor_get(v___x_1091_, 0);
v_hypQueue_1094_ = lean_ctor_get(v___x_1091_, 1);
v_usedHyps_1095_ = lean_ctor_get(v___x_1091_, 2);
v_didChange_1096_ = lean_ctor_get_uint8(v___x_1091_, sizeof(void*)*6);
v_solverTimeBudgetMs_1097_ = lean_ctor_get(v___x_1091_, 4);
v_roundBudget_1098_ = lean_ctor_get(v___x_1091_, 5);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1100_ = v___x_1091_;
v_isShared_1101_ = v_isSharedCheck_1120_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_roundBudget_1098_);
lean_inc(v_solverTimeBudgetMs_1097_);
lean_inc(v_theoryState_1092_);
lean_inc(v_usedHyps_1095_);
lean_inc(v_hypQueue_1094_);
lean_inc(v_satExpr_1093_);
lean_dec(v___x_1091_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1120_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_funState_1102_; lean_object* v_bitvecState_1103_; lean_object* v_eprState_1104_; lean_object* v_satSolver_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1118_; 
v_funState_1102_ = lean_ctor_get(v_theoryState_1092_, 0);
v_bitvecState_1103_ = lean_ctor_get(v_theoryState_1092_, 1);
v_eprState_1104_ = lean_ctor_get(v_theoryState_1092_, 2);
v_satSolver_1105_ = lean_ctor_get(v_theoryState_1092_, 4);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_theoryState_1092_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_theoryState_1092_, 3);
lean_dec(v_unused_1119_);
v___x_1107_ = v_theoryState_1092_;
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_satSolver_1105_);
lean_inc(v_eprState_1104_);
lean_inc(v_bitvecState_1103_);
lean_inc(v_funState_1102_);
lean_dec(v_theoryState_1092_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_box(0);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 3, v_caches_1088_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_funState_1102_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_bitvecState_1103_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_eprState_1104_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_caches_1088_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_satSolver_1105_);
v___x_1111_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 3, v___x_1111_);
v___x_1113_ = v___x_1100_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_satExpr_1093_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_hypQueue_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_usedHyps_1095_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_solverTimeBudgetMs_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_roundBudget_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*6, v_didChange_1096_);
v___x_1113_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_st_ref_put(v_a_1089_, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1109_);
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg___boxed(lean_object* v_caches_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(v_caches_1121_, v_a_1122_);
lean_dec(v_a_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(lean_object* v_caches_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v_theoryState_1142_; lean_object* v_satExpr_1143_; lean_object* v_hypQueue_1144_; lean_object* v_usedHyps_1145_; uint8_t v_didChange_1146_; lean_object* v_solverTimeBudgetMs_1147_; lean_object* v_roundBudget_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1170_; 
v___x_1141_ = lean_st_ref_take(v_a_1127_);
v_theoryState_1142_ = lean_ctor_get(v___x_1141_, 3);
v_satExpr_1143_ = lean_ctor_get(v___x_1141_, 0);
v_hypQueue_1144_ = lean_ctor_get(v___x_1141_, 1);
v_usedHyps_1145_ = lean_ctor_get(v___x_1141_, 2);
v_didChange_1146_ = lean_ctor_get_uint8(v___x_1141_, sizeof(void*)*6);
v_solverTimeBudgetMs_1147_ = lean_ctor_get(v___x_1141_, 4);
v_roundBudget_1148_ = lean_ctor_get(v___x_1141_, 5);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1150_ = v___x_1141_;
v_isShared_1151_ = v_isSharedCheck_1170_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_roundBudget_1148_);
lean_inc(v_solverTimeBudgetMs_1147_);
lean_inc(v_theoryState_1142_);
lean_inc(v_usedHyps_1145_);
lean_inc(v_hypQueue_1144_);
lean_inc(v_satExpr_1143_);
lean_dec(v___x_1141_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1170_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_funState_1152_; lean_object* v_bitvecState_1153_; lean_object* v_eprState_1154_; lean_object* v_satSolver_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1168_; 
v_funState_1152_ = lean_ctor_get(v_theoryState_1142_, 0);
v_bitvecState_1153_ = lean_ctor_get(v_theoryState_1142_, 1);
v_eprState_1154_ = lean_ctor_get(v_theoryState_1142_, 2);
v_satSolver_1155_ = lean_ctor_get(v_theoryState_1142_, 4);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_theoryState_1142_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_theoryState_1142_, 3);
lean_dec(v_unused_1169_);
v___x_1157_ = v_theoryState_1142_;
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_satSolver_1155_);
lean_inc(v_eprState_1154_);
lean_inc(v_bitvecState_1153_);
lean_inc(v_funState_1152_);
lean_dec(v_theoryState_1142_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 3, v_caches_1125_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_funState_1152_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_bitvecState_1153_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_eprState_1154_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_caches_1125_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_satSolver_1155_);
v___x_1161_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 3, v___x_1161_);
v___x_1163_ = v___x_1150_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_satExpr_1143_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_hypQueue_1144_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_usedHyps_1145_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_solverTimeBudgetMs_1147_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v_roundBudget_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*6, v_didChange_1146_);
v___x_1163_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_st_ref_put(v_a_1127_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1159_);
return v___x_1165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___boxed(lean_object* v_caches_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(v_caches_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(lean_object* v_ctx_1188_, lean_object* v_x_1189_, lean_object* v_goal_1190_, lean_object* v_reflectionResult_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v_config_1206_; lean_object* v_satExpr_1207_; lean_object* v_unusedHypotheses_1208_; lean_object* v_timeout_1209_; lean_object* v_cegarRounds_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1205_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1206_ = lean_ctor_get(v_ctx_1188_, 5);
v_satExpr_1207_ = lean_ctor_get(v_reflectionResult_1191_, 0);
v_unusedHypotheses_1208_ = lean_ctor_get(v_reflectionResult_1191_, 1);
v_timeout_1209_ = lean_ctor_get(v_config_1206_, 0);
v_cegarRounds_1210_ = lean_ctor_get(v_config_1206_, 2);
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1212_ = 1;
v___x_1213_ = lean_unsigned_to_nat(1000u);
v___x_1214_ = lean_nat_mul(v_timeout_1209_, v___x_1213_);
lean_inc(v_cegarRounds_1210_);
lean_inc_ref(v_satExpr_1207_);
v___x_1215_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1215_, 0, v_satExpr_1207_);
lean_ctor_set(v___x_1215_, 1, v___x_1211_);
lean_ctor_set(v___x_1215_, 2, v___x_1211_);
lean_ctor_set(v___x_1215_, 3, v___x_1205_);
lean_ctor_set(v___x_1215_, 4, v___x_1214_);
lean_ctor_set(v___x_1215_, 5, v_cegarRounds_1210_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*6, v___x_1212_);
lean_inc_ref(v_unusedHypotheses_1208_);
v___x_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1216_, 0, v_goal_1190_);
lean_ctor_set(v___x_1216_, 1, v_unusedHypotheses_1208_);
lean_ctor_set(v___x_1216_, 2, v_ctx_1188_);
v___x_1217_ = lean_st_mk_ref(v___x_1215_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
lean_inc(v_a_1197_);
lean_inc_ref(v_a_1196_);
lean_inc(v_a_1195_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc(v___x_1217_);
v___x_1218_ = lean_apply_15(v_x_1189_, v___x_1216_, v___x_1217_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_st_ref_get(v___x_1217_);
lean_dec(v___x_1217_);
lean_dec(v___x_1223_);
if (v_isShared_1222_ == 0)
{
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1219_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_dec(v___x_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg___boxed(lean_object** _args){
lean_object* v_ctx_1228_ = _args[0];
lean_object* v_x_1229_ = _args[1];
lean_object* v_goal_1230_ = _args[2];
lean_object* v_reflectionResult_1231_ = _args[3];
lean_object* v_a_1232_ = _args[4];
lean_object* v_a_1233_ = _args[5];
lean_object* v_a_1234_ = _args[6];
lean_object* v_a_1235_ = _args[7];
lean_object* v_a_1236_ = _args[8];
lean_object* v_a_1237_ = _args[9];
lean_object* v_a_1238_ = _args[10];
lean_object* v_a_1239_ = _args[11];
lean_object* v_a_1240_ = _args[12];
lean_object* v_a_1241_ = _args[13];
lean_object* v_a_1242_ = _args[14];
lean_object* v_a_1243_ = _args[15];
lean_object* v_a_1244_ = _args[16];
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(v_ctx_1228_, v_x_1229_, v_goal_1230_, v_reflectionResult_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_reflectionResult_1231_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_object* v_00_u03b1_1246_, lean_object* v_ctx_1247_, lean_object* v_x_1248_, lean_object* v_goal_1249_, lean_object* v_reflectionResult_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_config_1265_; lean_object* v_satExpr_1266_; lean_object* v_unusedHypotheses_1267_; lean_object* v_timeout_1268_; lean_object* v_cegarRounds_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1264_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1265_ = lean_ctor_get(v_ctx_1247_, 5);
v_satExpr_1266_ = lean_ctor_get(v_reflectionResult_1250_, 0);
v_unusedHypotheses_1267_ = lean_ctor_get(v_reflectionResult_1250_, 1);
v_timeout_1268_ = lean_ctor_get(v_config_1265_, 0);
v_cegarRounds_1269_ = lean_ctor_get(v_config_1265_, 2);
v___x_1270_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1271_ = 1;
v___x_1272_ = lean_unsigned_to_nat(1000u);
v___x_1273_ = lean_nat_mul(v_timeout_1268_, v___x_1272_);
lean_inc(v_cegarRounds_1269_);
lean_inc_ref(v_satExpr_1266_);
v___x_1274_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1274_, 0, v_satExpr_1266_);
lean_ctor_set(v___x_1274_, 1, v___x_1270_);
lean_ctor_set(v___x_1274_, 2, v___x_1270_);
lean_ctor_set(v___x_1274_, 3, v___x_1264_);
lean_ctor_set(v___x_1274_, 4, v___x_1273_);
lean_ctor_set(v___x_1274_, 5, v_cegarRounds_1269_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*6, v___x_1271_);
lean_inc_ref(v_unusedHypotheses_1267_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_goal_1249_);
lean_ctor_set(v___x_1275_, 1, v_unusedHypotheses_1267_);
lean_ctor_set(v___x_1275_, 2, v_ctx_1247_);
v___x_1276_ = lean_st_mk_ref(v___x_1274_);
lean_inc(v_a_1262_);
lean_inc_ref(v_a_1261_);
lean_inc(v_a_1260_);
lean_inc_ref(v_a_1259_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc(v_a_1251_);
lean_inc(v___x_1276_);
v___x_1277_ = lean_apply_15(v_x_1248_, v___x_1275_, v___x_1276_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, lean_box(0));
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1286_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1286_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_st_ref_get(v___x_1276_);
lean_dec(v___x_1276_);
lean_dec(v___x_1282_);
if (v_isShared_1281_ == 0)
{
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1278_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_dec(v___x_1276_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___boxed(lean_object** _args){
lean_object* v_00_u03b1_1287_ = _args[0];
lean_object* v_ctx_1288_ = _args[1];
lean_object* v_x_1289_ = _args[2];
lean_object* v_goal_1290_ = _args[3];
lean_object* v_reflectionResult_1291_ = _args[4];
lean_object* v_a_1292_ = _args[5];
lean_object* v_a_1293_ = _args[6];
lean_object* v_a_1294_ = _args[7];
lean_object* v_a_1295_ = _args[8];
lean_object* v_a_1296_ = _args[9];
lean_object* v_a_1297_ = _args[10];
lean_object* v_a_1298_ = _args[11];
lean_object* v_a_1299_ = _args[12];
lean_object* v_a_1300_ = _args[13];
lean_object* v_a_1301_ = _args[14];
lean_object* v_a_1302_ = _args[15];
lean_object* v_a_1303_ = _args[16];
lean_object* v_a_1304_ = _args[17];
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run(v_00_u03b1_1287_, v_ctx_1288_, v_x_1289_, v_goal_1290_, v_reflectionResult_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_reflectionResult_1291_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_theoryState_1309_; lean_object* v_satSolver_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_st_ref_get(v_a_1306_);
v_theoryState_1309_ = lean_ctor_get(v___x_1308_, 3);
lean_inc_ref(v_theoryState_1309_);
lean_dec(v___x_1308_);
v_satSolver_1310_ = lean_ctor_get(v_theoryState_1309_, 4);
lean_inc_ref(v_satSolver_1310_);
lean_dec_ref(v_theoryState_1309_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_satSolver_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg___boxed(lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1312_);
lean_dec(v_a_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1316_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___boxed(lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
return v_res_1346_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_unsigned_to_nat(16u);
v___x_1352_ = lean_mk_array(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__1);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2);
v___x_1357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
lean_ctor_set(v___x_1357_, 2, v___x_1356_);
lean_ctor_set(v___x_1357_, 3, v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__5));
v___x_1363_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__2);
v___x_1364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
lean_ctor_set(v___x_1364_, 3, v___x_1362_);
lean_ctor_set(v___x_1364_, 4, v___x_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg(lean_object* v_x_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_goal_1378_; lean_object* v_tacticContext_1379_; lean_object* v___x_1380_; lean_object* v_config_1381_; lean_object* v_mode_1382_; lean_object* v_timeout_1383_; uint8_t v_trimProofs_1384_; uint8_t v_binaryProofs_1385_; uint8_t v_acNf_1386_; uint8_t v_andFlattening_1387_; uint8_t v_embeddedConstraintSubst_1388_; uint8_t v_graphviz_1389_; lean_object* v_maxSteps_1390_; uint8_t v_solverMode_1391_; uint8_t v_uf_1392_; lean_object* v_cegarRounds_1393_; uint8_t v_eprSymBreak_1394_; uint8_t v_eprProjections_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1494_; 
v_goal_1378_ = lean_ctor_get(v_a_1366_, 0);
v_tacticContext_1379_ = lean_ctor_get(v_a_1366_, 2);
lean_inc_ref(v_tacticContext_1379_);
v___x_1380_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1379_);
v_config_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_config_1381_);
v_mode_1382_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_mode_1382_);
lean_dec_ref(v___x_1380_);
v_timeout_1383_ = lean_ctor_get(v_config_1381_, 0);
v_trimProofs_1384_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3);
v_binaryProofs_1385_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 1);
v_acNf_1386_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 2);
v_andFlattening_1387_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1388_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 4);
v_graphviz_1389_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 8);
v_maxSteps_1390_ = lean_ctor_get(v_config_1381_, 1);
v_solverMode_1391_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 10);
v_uf_1392_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 11);
v_cegarRounds_1393_ = lean_ctor_get(v_config_1381_, 2);
v_eprSymBreak_1394_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 13);
v_eprProjections_1395_ = lean_ctor_get_uint8(v_config_1381_, sizeof(void*)*3 + 14);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_config_1381_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1397_ = v_config_1381_;
v_isShared_1398_ = v_isSharedCheck_1494_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_cegarRounds_1393_);
lean_inc(v_maxSteps_1390_);
lean_inc(v_timeout_1383_);
lean_dec(v_config_1381_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1494_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1402_; 
lean_inc(v_goal_1378_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v_goal_1378_);
v___x_1400_ = 0;
if (v_isShared_1398_ == 0)
{
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_timeout_1383_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_maxSteps_1390_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_cegarRounds_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3, v_trimProofs_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 1, v_binaryProofs_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 2, v_acNf_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 3, v_andFlattening_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 8, v_graphviz_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 10, v_solverMode_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 11, v_uf_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 13, v_eprSymBreak_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*3 + 14, v_eprProjections_1395_);
v___x_1402_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_theoryState_1406_; lean_object* v_satExpr_1407_; lean_object* v_hypQueue_1408_; lean_object* v_usedHyps_1409_; uint8_t v_didChange_1410_; lean_object* v_solverTimeBudgetMs_1411_; lean_object* v_roundBudget_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1492_; 
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3 + 5, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3 + 6, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3 + 7, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3 + 9, v___x_1400_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3 + 12, v___x_1400_);
v___x_1403_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__0));
v___x_1404_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1382_, v___x_1402_, v___x_1403_);
v___x_1405_ = lean_st_ref_take(v_a_1367_);
v_theoryState_1406_ = lean_ctor_get(v___x_1405_, 3);
v_satExpr_1407_ = lean_ctor_get(v___x_1405_, 0);
v_hypQueue_1408_ = lean_ctor_get(v___x_1405_, 1);
v_usedHyps_1409_ = lean_ctor_get(v___x_1405_, 2);
v_didChange_1410_ = lean_ctor_get_uint8(v___x_1405_, sizeof(void*)*6);
v_solverTimeBudgetMs_1411_ = lean_ctor_get(v___x_1405_, 4);
v_roundBudget_1412_ = lean_ctor_get(v___x_1405_, 5);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1414_ = v___x_1405_;
v_isShared_1415_ = v_isSharedCheck_1492_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_roundBudget_1412_);
lean_inc(v_solverTimeBudgetMs_1411_);
lean_inc(v_theoryState_1406_);
lean_inc(v_usedHyps_1409_);
lean_inc(v_hypQueue_1408_);
lean_inc(v_satExpr_1407_);
lean_dec(v___x_1405_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1492_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_funState_1416_; lean_object* v_bitvecState_1417_; lean_object* v_eprState_1418_; lean_object* v_preprocessCaches_1419_; lean_object* v_satSolver_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1491_; 
v_funState_1416_ = lean_ctor_get(v_theoryState_1406_, 0);
v_bitvecState_1417_ = lean_ctor_get(v_theoryState_1406_, 1);
v_eprState_1418_ = lean_ctor_get(v_theoryState_1406_, 2);
v_preprocessCaches_1419_ = lean_ctor_get(v_theoryState_1406_, 3);
v_satSolver_1420_ = lean_ctor_get(v_theoryState_1406_, 4);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_theoryState_1406_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1422_ = v_theoryState_1406_;
v_isShared_1423_ = v_isSharedCheck_1491_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_satSolver_1420_);
lean_inc(v_preprocessCaches_1419_);
lean_inc(v_eprState_1418_);
lean_inc(v_bitvecState_1417_);
lean_inc(v_funState_1416_);
lean_dec(v_theoryState_1406_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1491_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 3, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_funState_1416_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_bitvecState_1417_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_eprState_1418_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_satSolver_1420_);
v___x_1426_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 3, v___x_1426_);
v___x_1428_ = v___x_1414_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_satExpr_1407_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_hypQueue_1408_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_usedHyps_1409_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_solverTimeBudgetMs_1411_);
lean_ctor_set(v_reuseFailAlloc_1489_, 5, v_roundBudget_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, sizeof(void*)*6, v_didChange_1410_);
v___x_1428_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_typeAnalysis_1436_; lean_object* v_target_1437_; lean_object* v_hypotheses_1438_; uint8_t v_didChange_1439_; lean_object* v_eprBvProblem_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1487_; 
v___x_1429_ = lean_st_ref_put(v_a_1367_, v___x_1428_);
v___x_1430_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3);
v___x_1431_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__4));
v___x_1432_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6);
v___x_1433_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1433_, 0, v___x_1424_);
lean_ctor_set(v___x_1433_, 1, v___x_1430_);
lean_ctor_set(v___x_1433_, 2, v___x_1399_);
lean_ctor_set(v___x_1433_, 3, v___x_1431_);
lean_ctor_set(v___x_1433_, 4, v___x_1432_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*5, v___x_1400_);
v___x_1434_ = lean_st_mk_ref(v___x_1433_);
v___x_1435_ = lean_st_ref_take(v___x_1434_);
v_typeAnalysis_1436_ = lean_ctor_get(v___x_1435_, 1);
v_target_1437_ = lean_ctor_get(v___x_1435_, 2);
v_hypotheses_1438_ = lean_ctor_get(v___x_1435_, 3);
v_didChange_1439_ = lean_ctor_get_uint8(v___x_1435_, sizeof(void*)*5);
v_eprBvProblem_1440_ = lean_ctor_get(v___x_1435_, 4);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1435_, 0);
lean_dec(v_unused_1488_);
v___x_1442_ = v___x_1435_;
v_isShared_1443_ = v_isSharedCheck_1487_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_eprBvProblem_1440_);
lean_inc(v_hypotheses_1438_);
lean_inc(v_target_1437_);
lean_inc(v_typeAnalysis_1436_);
lean_dec(v___x_1435_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1487_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_preprocessCaches_1419_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_preprocessCaches_1419_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_typeAnalysis_1436_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_target_1437_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_hypotheses_1438_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_eprBvProblem_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*5, v_didChange_1439_);
v___x_1445_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_st_ref_put(v___x_1434_, v___x_1445_);
lean_inc(v_a_1376_);
lean_inc_ref(v_a_1375_);
lean_inc(v_a_1374_);
lean_inc_ref(v_a_1373_);
lean_inc(v_a_1372_);
lean_inc_ref(v_a_1371_);
lean_inc(v_a_1370_);
lean_inc_ref(v_a_1369_);
lean_inc(v_a_1368_);
lean_inc(v___x_1434_);
v___x_1447_ = lean_apply_12(v_x_1365_, v___x_1404_, v___x_1434_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, lean_box(0));
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1485_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1485_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1485_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v_caches_1453_; lean_object* v___x_1454_; lean_object* v_theoryState_1455_; lean_object* v_satExpr_1456_; lean_object* v_hypQueue_1457_; lean_object* v_usedHyps_1458_; uint8_t v_didChange_1459_; lean_object* v_solverTimeBudgetMs_1460_; lean_object* v_roundBudget_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1484_; 
v___x_1452_ = lean_st_ref_get(v___x_1434_);
lean_dec(v___x_1434_);
v_caches_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_caches_1453_);
lean_dec(v___x_1452_);
v___x_1454_ = lean_st_ref_take(v_a_1367_);
v_theoryState_1455_ = lean_ctor_get(v___x_1454_, 3);
v_satExpr_1456_ = lean_ctor_get(v___x_1454_, 0);
v_hypQueue_1457_ = lean_ctor_get(v___x_1454_, 1);
v_usedHyps_1458_ = lean_ctor_get(v___x_1454_, 2);
v_didChange_1459_ = lean_ctor_get_uint8(v___x_1454_, sizeof(void*)*6);
v_solverTimeBudgetMs_1460_ = lean_ctor_get(v___x_1454_, 4);
v_roundBudget_1461_ = lean_ctor_get(v___x_1454_, 5);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1463_ = v___x_1454_;
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_roundBudget_1461_);
lean_inc(v_solverTimeBudgetMs_1460_);
lean_inc(v_theoryState_1455_);
lean_inc(v_usedHyps_1458_);
lean_inc(v_hypQueue_1457_);
lean_inc(v_satExpr_1456_);
lean_dec(v___x_1454_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_funState_1465_; lean_object* v_bitvecState_1466_; lean_object* v_eprState_1467_; lean_object* v_satSolver_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1482_; 
v_funState_1465_ = lean_ctor_get(v_theoryState_1455_, 0);
v_bitvecState_1466_ = lean_ctor_get(v_theoryState_1455_, 1);
v_eprState_1467_ = lean_ctor_get(v_theoryState_1455_, 2);
v_satSolver_1468_ = lean_ctor_get(v_theoryState_1455_, 4);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_theoryState_1455_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_theoryState_1455_, 3);
lean_dec(v_unused_1483_);
v___x_1470_ = v_theoryState_1455_;
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_satSolver_1468_);
lean_inc(v_eprState_1467_);
lean_inc(v_bitvecState_1466_);
lean_inc(v_funState_1465_);
lean_dec(v_theoryState_1455_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 3, v_caches_1453_);
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_funState_1465_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_bitvecState_1466_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_eprState_1467_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_caches_1453_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_satSolver_1468_);
v___x_1473_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 3, v___x_1473_);
v___x_1475_ = v___x_1463_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_satExpr_1456_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_hypQueue_1457_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_usedHyps_1458_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_solverTimeBudgetMs_1460_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_roundBudget_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*6, v_didChange_1459_);
v___x_1475_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = lean_st_ref_put(v_a_1367_, v___x_1475_);
if (v_isShared_1451_ == 0)
{
v___x_1478_ = v___x_1450_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1448_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1434_);
return v___x_1447_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___boxed(lean_object* v_x_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg(v_x_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM(lean_object* v_00_u03b1_1509_, lean_object* v_x_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_goal_1526_; lean_object* v_tacticContext_1527_; lean_object* v___x_1528_; lean_object* v_config_1529_; lean_object* v_mode_1530_; lean_object* v_timeout_1531_; uint8_t v_trimProofs_1532_; uint8_t v_binaryProofs_1533_; uint8_t v_acNf_1534_; uint8_t v_andFlattening_1535_; uint8_t v_embeddedConstraintSubst_1536_; uint8_t v_graphviz_1537_; lean_object* v_maxSteps_1538_; uint8_t v_solverMode_1539_; uint8_t v_uf_1540_; lean_object* v_cegarRounds_1541_; uint8_t v_eprSymBreak_1542_; uint8_t v_eprProjections_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1642_; 
v_goal_1526_ = lean_ctor_get(v_a_1511_, 0);
v_tacticContext_1527_ = lean_ctor_get(v_a_1511_, 2);
lean_inc_ref(v_tacticContext_1527_);
v___x_1528_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1527_);
v_config_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_ref(v_config_1529_);
v_mode_1530_ = lean_ctor_get(v___x_1528_, 1);
lean_inc(v_mode_1530_);
lean_dec_ref(v___x_1528_);
v_timeout_1531_ = lean_ctor_get(v_config_1529_, 0);
v_trimProofs_1532_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3);
v_binaryProofs_1533_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 1);
v_acNf_1534_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 2);
v_andFlattening_1535_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1536_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 4);
v_graphviz_1537_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 8);
v_maxSteps_1538_ = lean_ctor_get(v_config_1529_, 1);
v_solverMode_1539_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 10);
v_uf_1540_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 11);
v_cegarRounds_1541_ = lean_ctor_get(v_config_1529_, 2);
v_eprSymBreak_1542_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 13);
v_eprProjections_1543_ = lean_ctor_get_uint8(v_config_1529_, sizeof(void*)*3 + 14);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_config_1529_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1545_ = v_config_1529_;
v_isShared_1546_ = v_isSharedCheck_1642_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_cegarRounds_1541_);
lean_inc(v_maxSteps_1538_);
lean_inc(v_timeout_1531_);
lean_dec(v_config_1529_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1642_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1550_; 
lean_inc(v_goal_1526_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_goal_1526_);
v___x_1548_ = 0;
if (v_isShared_1546_ == 0)
{
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 3, 15);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_timeout_1531_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_maxSteps_1538_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_cegarRounds_1541_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3, v_trimProofs_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 1, v_binaryProofs_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 2, v_acNf_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 3, v_andFlattening_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 8, v_graphviz_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 10, v_solverMode_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 11, v_uf_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 13, v_eprSymBreak_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3 + 14, v_eprProjections_1543_);
v___x_1550_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_theoryState_1554_; lean_object* v_satExpr_1555_; lean_object* v_hypQueue_1556_; lean_object* v_usedHyps_1557_; uint8_t v_didChange_1558_; lean_object* v_solverTimeBudgetMs_1559_; lean_object* v_roundBudget_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1640_; 
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 5, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 6, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 7, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 9, v___x_1548_);
lean_ctor_set_uint8(v___x_1550_, sizeof(void*)*3 + 12, v___x_1548_);
v___x_1551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__0));
v___x_1552_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1530_, v___x_1550_, v___x_1551_);
v___x_1553_ = lean_st_ref_take(v_a_1512_);
v_theoryState_1554_ = lean_ctor_get(v___x_1553_, 3);
v_satExpr_1555_ = lean_ctor_get(v___x_1553_, 0);
v_hypQueue_1556_ = lean_ctor_get(v___x_1553_, 1);
v_usedHyps_1557_ = lean_ctor_get(v___x_1553_, 2);
v_didChange_1558_ = lean_ctor_get_uint8(v___x_1553_, sizeof(void*)*6);
v_solverTimeBudgetMs_1559_ = lean_ctor_get(v___x_1553_, 4);
v_roundBudget_1560_ = lean_ctor_get(v___x_1553_, 5);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1562_ = v___x_1553_;
v_isShared_1563_ = v_isSharedCheck_1640_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_roundBudget_1560_);
lean_inc(v_solverTimeBudgetMs_1559_);
lean_inc(v_theoryState_1554_);
lean_inc(v_usedHyps_1557_);
lean_inc(v_hypQueue_1556_);
lean_inc(v_satExpr_1555_);
lean_dec(v___x_1553_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1640_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_funState_1564_; lean_object* v_bitvecState_1565_; lean_object* v_eprState_1566_; lean_object* v_preprocessCaches_1567_; lean_object* v_satSolver_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1639_; 
v_funState_1564_ = lean_ctor_get(v_theoryState_1554_, 0);
v_bitvecState_1565_ = lean_ctor_get(v_theoryState_1554_, 1);
v_eprState_1566_ = lean_ctor_get(v_theoryState_1554_, 2);
v_preprocessCaches_1567_ = lean_ctor_get(v_theoryState_1554_, 3);
v_satSolver_1568_ = lean_ctor_get(v_theoryState_1554_, 4);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_theoryState_1554_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1570_ = v_theoryState_1554_;
v_isShared_1571_ = v_isSharedCheck_1639_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_satSolver_1568_);
lean_inc(v_preprocessCaches_1567_);
lean_inc(v_eprState_1566_);
lean_inc(v_bitvecState_1565_);
lean_inc(v_funState_1564_);
lean_dec(v_theoryState_1554_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1639_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__7);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 3, v___x_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_funState_1564_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_bitvecState_1565_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_eprState_1566_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_satSolver_1568_);
v___x_1574_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 3, v___x_1574_);
v___x_1576_ = v___x_1562_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_satExpr_1555_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_hypQueue_1556_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_usedHyps_1557_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_solverTimeBudgetMs_1559_);
lean_ctor_set(v_reuseFailAlloc_1637_, 5, v_roundBudget_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1637_, sizeof(void*)*6, v_didChange_1558_);
v___x_1576_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_typeAnalysis_1584_; lean_object* v_target_1585_; lean_object* v_hypotheses_1586_; uint8_t v_didChange_1587_; lean_object* v_eprBvProblem_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1635_; 
v___x_1577_ = lean_st_ref_put(v_a_1512_, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__3);
v___x_1579_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__4));
v___x_1580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___redArg___closed__6);
v___x_1581_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1581_, 0, v___x_1572_);
lean_ctor_set(v___x_1581_, 1, v___x_1578_);
lean_ctor_set(v___x_1581_, 2, v___x_1547_);
lean_ctor_set(v___x_1581_, 3, v___x_1579_);
lean_ctor_set(v___x_1581_, 4, v___x_1580_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*5, v___x_1548_);
v___x_1582_ = lean_st_mk_ref(v___x_1581_);
v___x_1583_ = lean_st_ref_take(v___x_1582_);
v_typeAnalysis_1584_ = lean_ctor_get(v___x_1583_, 1);
v_target_1585_ = lean_ctor_get(v___x_1583_, 2);
v_hypotheses_1586_ = lean_ctor_get(v___x_1583_, 3);
v_didChange_1587_ = lean_ctor_get_uint8(v___x_1583_, sizeof(void*)*5);
v_eprBvProblem_1588_ = lean_ctor_get(v___x_1583_, 4);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v___x_1583_, 0);
lean_dec(v_unused_1636_);
v___x_1590_ = v___x_1583_;
v_isShared_1591_ = v_isSharedCheck_1635_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_eprBvProblem_1588_);
lean_inc(v_hypotheses_1586_);
lean_inc(v_target_1585_);
lean_inc(v_typeAnalysis_1584_);
lean_dec(v___x_1583_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1635_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_preprocessCaches_1567_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_preprocessCaches_1567_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_typeAnalysis_1584_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_target_1585_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_hypotheses_1586_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_eprBvProblem_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1634_, sizeof(void*)*5, v_didChange_1587_);
v___x_1593_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_st_ref_put(v___x_1582_, v___x_1593_);
lean_inc(v_a_1524_);
lean_inc_ref(v_a_1523_);
lean_inc(v_a_1522_);
lean_inc_ref(v_a_1521_);
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
lean_inc(v_a_1516_);
lean_inc(v___x_1582_);
v___x_1595_ = lean_apply_12(v_x_1510_, v___x_1552_, v___x_1582_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, lean_box(0));
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1633_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1633_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1633_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v_caches_1601_; lean_object* v___x_1602_; lean_object* v_theoryState_1603_; lean_object* v_satExpr_1604_; lean_object* v_hypQueue_1605_; lean_object* v_usedHyps_1606_; uint8_t v_didChange_1607_; lean_object* v_solverTimeBudgetMs_1608_; lean_object* v_roundBudget_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1632_; 
v___x_1600_ = lean_st_ref_get(v___x_1582_);
lean_dec(v___x_1582_);
v_caches_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_caches_1601_);
lean_dec(v___x_1600_);
v___x_1602_ = lean_st_ref_take(v_a_1512_);
v_theoryState_1603_ = lean_ctor_get(v___x_1602_, 3);
v_satExpr_1604_ = lean_ctor_get(v___x_1602_, 0);
v_hypQueue_1605_ = lean_ctor_get(v___x_1602_, 1);
v_usedHyps_1606_ = lean_ctor_get(v___x_1602_, 2);
v_didChange_1607_ = lean_ctor_get_uint8(v___x_1602_, sizeof(void*)*6);
v_solverTimeBudgetMs_1608_ = lean_ctor_get(v___x_1602_, 4);
v_roundBudget_1609_ = lean_ctor_get(v___x_1602_, 5);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1611_ = v___x_1602_;
v_isShared_1612_ = v_isSharedCheck_1632_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_roundBudget_1609_);
lean_inc(v_solverTimeBudgetMs_1608_);
lean_inc(v_theoryState_1603_);
lean_inc(v_usedHyps_1606_);
lean_inc(v_hypQueue_1605_);
lean_inc(v_satExpr_1604_);
lean_dec(v___x_1602_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1632_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_funState_1613_; lean_object* v_bitvecState_1614_; lean_object* v_eprState_1615_; lean_object* v_satSolver_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1630_; 
v_funState_1613_ = lean_ctor_get(v_theoryState_1603_, 0);
v_bitvecState_1614_ = lean_ctor_get(v_theoryState_1603_, 1);
v_eprState_1615_ = lean_ctor_get(v_theoryState_1603_, 2);
v_satSolver_1616_ = lean_ctor_get(v_theoryState_1603_, 4);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_theoryState_1603_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_theoryState_1603_, 3);
lean_dec(v_unused_1631_);
v___x_1618_ = v_theoryState_1603_;
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_satSolver_1616_);
lean_inc(v_eprState_1615_);
lean_inc(v_bitvecState_1614_);
lean_inc(v_funState_1613_);
lean_dec(v_theoryState_1603_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 3, v_caches_1601_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_funState_1613_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_bitvecState_1614_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_eprState_1615_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v_caches_1601_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_satSolver_1616_);
v___x_1621_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 3, v___x_1621_);
v___x_1623_ = v___x_1611_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_satExpr_1604_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_hypQueue_1605_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_usedHyps_1606_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_solverTimeBudgetMs_1608_);
lean_ctor_set(v_reuseFailAlloc_1628_, 5, v_roundBudget_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*6, v_didChange_1607_);
v___x_1623_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_st_ref_put(v_a_1512_, v___x_1623_);
if (v_isShared_1599_ == 0)
{
v___x_1626_ = v___x_1598_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1596_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1582_);
return v___x_1595_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM___boxed(lean_object** _args){
lean_object* v_00_u03b1_1643_ = _args[0];
lean_object* v_x_1644_ = _args[1];
lean_object* v_a_1645_ = _args[2];
lean_object* v_a_1646_ = _args[3];
lean_object* v_a_1647_ = _args[4];
lean_object* v_a_1648_ = _args[5];
lean_object* v_a_1649_ = _args[6];
lean_object* v_a_1650_ = _args[7];
lean_object* v_a_1651_ = _args[8];
lean_object* v_a_1652_ = _args[9];
lean_object* v_a_1653_ = _args[10];
lean_object* v_a_1654_ = _args[11];
lean_object* v_a_1655_ = _args[12];
lean_object* v_a_1656_ = _args[13];
lean_object* v_a_1657_ = _args[14];
lean_object* v_a_1658_ = _args[15];
lean_object* v_a_1659_ = _args[16];
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Meta_Tactic_BVDecide_CegarM_liftPreProcessM(v_00_u03b1_1643_, v_x_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1660_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_instMonadEIO___redArg();
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_toApplicative_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1749_; 
v___x_1679_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0);
v___x_1680_ = l_StateRefT_x27_instMonad___redArg(v___x_1679_);
v_toApplicative_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1680_, 1);
lean_dec(v_unused_1750_);
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1749_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_toApplicative_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1749_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_toFunctor_1685_; lean_object* v_toSeq_1686_; lean_object* v_toSeqLeft_1687_; lean_object* v_toSeqRight_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1747_; 
v_toFunctor_1685_ = lean_ctor_get(v_toApplicative_1681_, 0);
v_toSeq_1686_ = lean_ctor_get(v_toApplicative_1681_, 2);
v_toSeqLeft_1687_ = lean_ctor_get(v_toApplicative_1681_, 3);
v_toSeqRight_1688_ = lean_ctor_get(v_toApplicative_1681_, 4);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_toApplicative_1681_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_dec(v_unused_1748_);
v___x_1690_ = v_toApplicative_1681_;
v_isShared_1691_ = v_isSharedCheck_1747_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_toSeqRight_1688_);
lean_inc(v_toSeqLeft_1687_);
lean_inc(v_toSeq_1686_);
lean_inc(v_toFunctor_1685_);
lean_dec(v_toApplicative_1681_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1747_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___x_1701_; 
v___f_1692_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1));
v___f_1693_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1685_);
v___f_1694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1694_, 0, v_toFunctor_1685_);
v___f_1695_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1695_, 0, v_toFunctor_1685_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___f_1694_);
lean_ctor_set(v___x_1696_, 1, v___f_1695_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeqRight_1688_);
v___f_1698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1698_, 0, v_toSeqLeft_1687_);
v___f_1699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1699_, 0, v_toSeq_1686_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v___f_1697_);
lean_ctor_set(v___x_1690_, 3, v___f_1698_);
lean_ctor_set(v___x_1690_, 2, v___f_1699_);
lean_ctor_set(v___x_1690_, 1, v___f_1692_);
lean_ctor_set(v___x_1690_, 0, v___x_1696_);
v___x_1701_ = v___x_1690_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___f_1692_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v___f_1699_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v___f_1698_);
lean_ctor_set(v_reuseFailAlloc_1746_, 4, v___f_1697_);
v___x_1701_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___f_1693_);
lean_ctor_set(v___x_1683_, 0, v___x_1701_);
v___x_1703_ = v___x_1683_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___f_1693_);
v___x_1703_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v_toApplicative_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1743_; 
v___x_1704_ = l_StateRefT_x27_instMonad___redArg(v___x_1703_);
v_toApplicative_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v___x_1704_, 1);
lean_dec(v_unused_1744_);
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1743_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_toApplicative_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1743_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_toFunctor_1709_; lean_object* v_toSeq_1710_; lean_object* v_toSeqLeft_1711_; lean_object* v_toSeqRight_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1741_; 
v_toFunctor_1709_ = lean_ctor_get(v_toApplicative_1705_, 0);
v_toSeq_1710_ = lean_ctor_get(v_toApplicative_1705_, 2);
v_toSeqLeft_1711_ = lean_ctor_get(v_toApplicative_1705_, 3);
v_toSeqRight_1712_ = lean_ctor_get(v_toApplicative_1705_, 4);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_toApplicative_1705_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_toApplicative_1705_, 1);
lean_dec(v_unused_1742_);
v___x_1714_ = v_toApplicative_1705_;
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_toSeqRight_1712_);
lean_inc(v_toSeqLeft_1711_);
lean_inc(v_toSeq_1710_);
lean_inc(v_toFunctor_1709_);
lean_dec(v_toApplicative_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1741_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___f_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___x_1725_; 
v___f_1716_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3));
v___f_1717_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4));
lean_inc_ref(v_toFunctor_1709_);
v___f_1718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1718_, 0, v_toFunctor_1709_);
v___f_1719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1719_, 0, v_toFunctor_1709_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___f_1718_);
lean_ctor_set(v___x_1720_, 1, v___f_1719_);
v___f_1721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1721_, 0, v_toSeqRight_1712_);
v___f_1722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1722_, 0, v_toSeqLeft_1711_);
v___f_1723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1723_, 0, v_toSeq_1710_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v___f_1721_);
lean_ctor_set(v___x_1714_, 3, v___f_1722_);
lean_ctor_set(v___x_1714_, 2, v___f_1723_);
lean_ctor_set(v___x_1714_, 1, v___f_1716_);
lean_ctor_set(v___x_1714_, 0, v___x_1720_);
v___x_1725_ = v___x_1714_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___f_1716_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v___f_1723_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v___f_1722_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v___f_1721_);
v___x_1725_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___f_1717_);
lean_ctor_set(v___x_1707_, 0, v___x_1725_);
v___x_1727_ = v___x_1707_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___f_1717_);
v___x_1727_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___f_1736_; lean_object* v___x_4587__overap_1737_; lean_object* v___x_1738_; 
v___x_1728_ = l_StateRefT_x27_instMonad___redArg(v___x_1727_);
v___x_1729_ = l_ReaderT_instMonad___redArg(v___x_1728_);
v___x_1730_ = l_StateRefT_x27_instMonad___redArg(v___x_1729_);
v___x_1731_ = l_ReaderT_instMonad___redArg(v___x_1730_);
v___x_1732_ = l_ReaderT_instMonad___redArg(v___x_1731_);
v___x_1733_ = l_StateRefT_x27_instMonad___redArg(v___x_1732_);
v___x_1734_ = lean_box(0);
v___x_1735_ = l_instInhabitedOfMonad___redArg(v___x_1733_, v___x_1734_);
v___f_1736_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1736_, 0, v___x_1735_);
v___x_4587__overap_1737_ = lean_panic_fn_borrowed(v___f_1736_, v_msg_1666_);
lean_dec_ref(v___f_1736_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1738_ = lean_apply_12(v___x_4587__overap_1737_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1738_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___boxed(lean_object* v_msg_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v_msg_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
return v_x_1765_;
}
else
{
lean_object* v_key_1767_; lean_object* v_value_1768_; lean_object* v_tail_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1792_; 
v_key_1767_ = lean_ctor_get(v_x_1766_, 0);
v_value_1768_ = lean_ctor_get(v_x_1766_, 1);
v_tail_1769_ = lean_ctor_get(v_x_1766_, 2);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1771_ = v_x_1766_;
v_isShared_1772_ = v_isSharedCheck_1792_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_tail_1769_);
lean_inc(v_value_1768_);
lean_inc(v_key_1767_);
lean_dec(v_x_1766_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1792_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; uint64_t v___x_1774_; uint64_t v___x_1775_; uint64_t v___x_1776_; uint64_t v_fold_1777_; uint64_t v___x_1778_; uint64_t v___x_1779_; uint64_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; size_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1773_ = lean_array_get_size(v_x_1765_);
v___x_1774_ = l_Lean_Expr_hash(v_key_1767_);
v___x_1775_ = 32ULL;
v___x_1776_ = lean_uint64_shift_right(v___x_1774_, v___x_1775_);
v_fold_1777_ = lean_uint64_xor(v___x_1774_, v___x_1776_);
v___x_1778_ = 16ULL;
v___x_1779_ = lean_uint64_shift_right(v_fold_1777_, v___x_1778_);
v___x_1780_ = lean_uint64_xor(v_fold_1777_, v___x_1779_);
v___x_1781_ = lean_uint64_to_usize(v___x_1780_);
v___x_1782_ = lean_usize_of_nat(v___x_1773_);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_sub(v___x_1782_, v___x_1783_);
v___x_1785_ = lean_usize_land(v___x_1781_, v___x_1784_);
v___x_1786_ = lean_array_uget_borrowed(v_x_1765_, v___x_1785_);
lean_inc(v___x_1786_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 2, v___x_1786_);
v___x_1788_ = v___x_1771_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_key_1767_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_value_1768_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_array_uset(v_x_1765_, v___x_1785_, v___x_1788_);
v_x_1765_ = v___x_1789_;
v_x_1766_ = v_tail_1769_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(lean_object* v_i_1793_, lean_object* v_source_1794_, lean_object* v_target_1795_){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_array_get_size(v_source_1794_);
v___x_1797_ = lean_nat_dec_lt(v_i_1793_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_source_1794_);
lean_dec(v_i_1793_);
return v_target_1795_;
}
else
{
lean_object* v_es_1798_; lean_object* v___x_1799_; lean_object* v_source_1800_; lean_object* v_target_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_es_1798_ = lean_array_fget(v_source_1794_, v_i_1793_);
v___x_1799_ = lean_box(0);
v_source_1800_ = lean_array_fset(v_source_1794_, v_i_1793_, v___x_1799_);
v_target_1801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_target_1795_, v_es_1798_);
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_i_1793_, v___x_1802_);
lean_dec(v_i_1793_);
v_i_1793_ = v___x_1803_;
v_source_1794_ = v_source_1800_;
v_target_1795_ = v_target_1801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(lean_object* v_data_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_nbuckets_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1806_ = lean_array_get_size(v_data_1805_);
v___x_1807_ = lean_unsigned_to_nat(2u);
v_nbuckets_1808_ = lean_nat_mul(v___x_1806_, v___x_1807_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_mk_array(v_nbuckets_1808_, v___x_1810_);
v___x_1812_ = lean_array_propagate_mark(v_data_1805_, v___x_1811_);
v___x_1813_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v___x_1809_, v_data_1805_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(lean_object* v_a_1814_, lean_object* v_x_1815_){
_start:
{
if (lean_obj_tag(v_x_1815_) == 0)
{
uint8_t v___x_1816_; 
v___x_1816_ = 0;
return v___x_1816_;
}
else
{
lean_object* v_key_1817_; lean_object* v_tail_1818_; uint8_t v___x_1819_; 
v_key_1817_ = lean_ctor_get(v_x_1815_, 0);
v_tail_1818_ = lean_ctor_get(v_x_1815_, 2);
v___x_1819_ = lean_expr_eqv(v_key_1817_, v_a_1814_);
if (v___x_1819_ == 0)
{
v_x_1815_ = v_tail_1818_;
goto _start;
}
else
{
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg___boxed(lean_object* v_a_1821_, lean_object* v_x_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1821_, v_x_1822_);
lean_dec(v_x_1822_);
lean_dec_ref(v_a_1821_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(lean_object* v_a_1825_, lean_object* v_b_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_dec(v_b_1826_);
lean_dec_ref(v_a_1825_);
return v_x_1827_;
}
else
{
lean_object* v_key_1828_; lean_object* v_value_1829_; lean_object* v_tail_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1842_; 
v_key_1828_ = lean_ctor_get(v_x_1827_, 0);
v_value_1829_ = lean_ctor_get(v_x_1827_, 1);
v_tail_1830_ = lean_ctor_get(v_x_1827_, 2);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1832_ = v_x_1827_;
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tail_1830_);
lean_inc(v_value_1829_);
lean_inc(v_key_1828_);
lean_dec(v_x_1827_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_expr_eqv(v_key_1828_, v_a_1825_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1825_, v_b_1826_, v_tail_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 2, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_key_1828_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_value_1829_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_value_1829_);
lean_dec(v_key_1828_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_b_1826_);
lean_ctor_set(v___x_1832_, 0, v_a_1825_);
v___x_1840_ = v___x_1832_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1825_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_b_1826_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_tail_1830_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(lean_object* v_m_1843_, lean_object* v_a_1844_, lean_object* v_b_1845_){
_start:
{
lean_object* v_size_1846_; lean_object* v_buckets_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1890_; 
v_size_1846_ = lean_ctor_get(v_m_1843_, 0);
v_buckets_1847_ = lean_ctor_get(v_m_1843_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_m_1843_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1849_ = v_m_1843_;
v_isShared_1850_ = v_isSharedCheck_1890_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_buckets_1847_);
lean_inc(v_size_1846_);
lean_dec(v_m_1843_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1890_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; uint64_t v___x_1852_; uint64_t v___x_1853_; uint64_t v___x_1854_; uint64_t v_fold_1855_; uint64_t v___x_1856_; uint64_t v___x_1857_; uint64_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; lean_object* v_bkt_1864_; uint8_t v___x_1865_; 
v___x_1851_ = lean_array_get_size(v_buckets_1847_);
v___x_1852_ = l_Lean_Expr_hash(v_a_1844_);
v___x_1853_ = 32ULL;
v___x_1854_ = lean_uint64_shift_right(v___x_1852_, v___x_1853_);
v_fold_1855_ = lean_uint64_xor(v___x_1852_, v___x_1854_);
v___x_1856_ = 16ULL;
v___x_1857_ = lean_uint64_shift_right(v_fold_1855_, v___x_1856_);
v___x_1858_ = lean_uint64_xor(v_fold_1855_, v___x_1857_);
v___x_1859_ = lean_uint64_to_usize(v___x_1858_);
v___x_1860_ = lean_usize_of_nat(v___x_1851_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_sub(v___x_1860_, v___x_1861_);
v___x_1863_ = lean_usize_land(v___x_1859_, v___x_1862_);
v_bkt_1864_ = lean_array_uget_borrowed(v_buckets_1847_, v___x_1863_);
v___x_1865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1844_, v_bkt_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v_size_x27_1867_; lean_object* v___x_1868_; lean_object* v_buckets_x27_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1866_ = lean_unsigned_to_nat(1u);
v_size_x27_1867_ = lean_nat_add(v_size_1846_, v___x_1866_);
lean_dec(v_size_1846_);
lean_inc(v_bkt_1864_);
v___x_1868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1844_);
lean_ctor_set(v___x_1868_, 1, v_b_1845_);
lean_ctor_set(v___x_1868_, 2, v_bkt_1864_);
v_buckets_x27_1869_ = lean_array_uset(v_buckets_1847_, v___x_1863_, v___x_1868_);
v___x_1870_ = lean_unsigned_to_nat(4u);
v___x_1871_ = lean_nat_mul(v_size_x27_1867_, v___x_1870_);
v___x_1872_ = lean_unsigned_to_nat(3u);
v___x_1873_ = lean_nat_div(v___x_1871_, v___x_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_array_get_size(v_buckets_x27_1869_);
v___x_1875_ = lean_nat_dec_le(v___x_1873_, v___x_1874_);
lean_dec(v___x_1873_);
if (v___x_1875_ == 0)
{
lean_object* v_val_1876_; lean_object* v___x_1878_; 
v_val_1876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_buckets_x27_1869_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_val_1876_);
lean_ctor_set(v___x_1849_, 0, v_size_x27_1867_);
v___x_1878_ = v___x_1849_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_size_x27_1867_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_val_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
else
{
lean_object* v___x_1881_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_buckets_x27_1869_);
lean_ctor_set(v___x_1849_, 0, v_size_x27_1867_);
v___x_1881_ = v___x_1849_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_size_x27_1867_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_buckets_x27_1869_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v_buckets_x27_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_inc(v_bkt_1864_);
v___x_1883_ = lean_box(0);
v_buckets_x27_1884_ = lean_array_uset(v_buckets_1847_, v___x_1863_, v___x_1883_);
v___x_1885_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1844_, v_b_1845_, v_bkt_1864_);
v___x_1886_ = lean_array_uset(v_buckets_x27_1884_, v___x_1863_, v___x_1885_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1886_);
v___x_1888_ = v___x_1849_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_size_1846_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(lean_object* v_a_1891_, lean_object* v_b_1892_, lean_object* v_x_1893_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_dec(v_b_1892_);
lean_dec(v_a_1891_);
return v_x_1893_;
}
else
{
lean_object* v_key_1894_; lean_object* v_value_1895_; lean_object* v_tail_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1908_; 
v_key_1894_ = lean_ctor_get(v_x_1893_, 0);
v_value_1895_ = lean_ctor_get(v_x_1893_, 1);
v_tail_1896_ = lean_ctor_get(v_x_1893_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1898_ = v_x_1893_;
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_tail_1896_);
lean_inc(v_value_1895_);
lean_inc(v_key_1894_);
lean_dec(v_x_1893_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_nat_dec_eq(v_key_1894_, v_a_1891_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1891_, v_b_1892_, v_tail_1896_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 2, v___x_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_key_1894_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_value_1895_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
else
{
lean_object* v___x_1906_; 
lean_dec(v_value_1895_);
lean_dec(v_key_1894_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_b_1892_);
lean_ctor_set(v___x_1898_, 0, v_a_1891_);
v___x_1906_ = v___x_1898_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1891_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_b_1892_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_tail_1896_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(lean_object* v_a_1909_, lean_object* v_x_1910_){
_start:
{
if (lean_obj_tag(v_x_1910_) == 0)
{
uint8_t v___x_1911_; 
v___x_1911_ = 0;
return v___x_1911_;
}
else
{
lean_object* v_key_1912_; lean_object* v_tail_1913_; uint8_t v___x_1914_; 
v_key_1912_ = lean_ctor_get(v_x_1910_, 0);
v_tail_1913_ = lean_ctor_get(v_x_1910_, 2);
v___x_1914_ = lean_nat_dec_eq(v_key_1912_, v_a_1909_);
if (v___x_1914_ == 0)
{
v_x_1910_ = v_tail_1913_;
goto _start;
}
else
{
return v___x_1914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg___boxed(lean_object* v_a_1916_, lean_object* v_x_1917_){
_start:
{
uint8_t v_res_1918_; lean_object* v_r_1919_; 
v_res_1918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1916_, v_x_1917_);
lean_dec(v_x_1917_);
lean_dec(v_a_1916_);
v_r_1919_ = lean_box(v_res_1918_);
return v_r_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
return v_x_1920_;
}
else
{
lean_object* v_key_1922_; lean_object* v_value_1923_; lean_object* v_tail_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1947_; 
v_key_1922_ = lean_ctor_get(v_x_1921_, 0);
v_value_1923_ = lean_ctor_get(v_x_1921_, 1);
v_tail_1924_ = lean_ctor_get(v_x_1921_, 2);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1926_ = v_x_1921_;
v_isShared_1927_ = v_isSharedCheck_1947_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_tail_1924_);
lean_inc(v_value_1923_);
lean_inc(v_key_1922_);
lean_dec(v_x_1921_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1947_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; uint64_t v___x_1929_; uint64_t v___x_1930_; uint64_t v___x_1931_; uint64_t v_fold_1932_; uint64_t v___x_1933_; uint64_t v___x_1934_; uint64_t v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1928_ = lean_array_get_size(v_x_1920_);
v___x_1929_ = lean_uint64_of_nat(v_key_1922_);
v___x_1930_ = 32ULL;
v___x_1931_ = lean_uint64_shift_right(v___x_1929_, v___x_1930_);
v_fold_1932_ = lean_uint64_xor(v___x_1929_, v___x_1931_);
v___x_1933_ = 16ULL;
v___x_1934_ = lean_uint64_shift_right(v_fold_1932_, v___x_1933_);
v___x_1935_ = lean_uint64_xor(v_fold_1932_, v___x_1934_);
v___x_1936_ = lean_uint64_to_usize(v___x_1935_);
v___x_1937_ = lean_usize_of_nat(v___x_1928_);
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_sub(v___x_1937_, v___x_1938_);
v___x_1940_ = lean_usize_land(v___x_1936_, v___x_1939_);
v___x_1941_ = lean_array_uget_borrowed(v_x_1920_, v___x_1940_);
lean_inc(v___x_1941_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 2, v___x_1941_);
v___x_1943_ = v___x_1926_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_key_1922_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_value_1923_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_array_uset(v_x_1920_, v___x_1940_, v___x_1943_);
v_x_1920_ = v___x_1944_;
v_x_1921_ = v_tail_1924_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(lean_object* v_i_1948_, lean_object* v_source_1949_, lean_object* v_target_1950_){
_start:
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = lean_array_get_size(v_source_1949_);
v___x_1952_ = lean_nat_dec_lt(v_i_1948_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec_ref(v_source_1949_);
lean_dec(v_i_1948_);
return v_target_1950_;
}
else
{
lean_object* v_es_1953_; lean_object* v___x_1954_; lean_object* v_source_1955_; lean_object* v_target_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_es_1953_ = lean_array_fget(v_source_1949_, v_i_1948_);
v___x_1954_ = lean_box(0);
v_source_1955_ = lean_array_fset(v_source_1949_, v_i_1948_, v___x_1954_);
v_target_1956_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1950_, v_es_1953_);
v___x_1957_ = lean_unsigned_to_nat(1u);
v___x_1958_ = lean_nat_add(v_i_1948_, v___x_1957_);
lean_dec(v_i_1948_);
v_i_1948_ = v___x_1958_;
v_source_1949_ = v_source_1955_;
v_target_1950_ = v_target_1956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(lean_object* v_data_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_nbuckets_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1961_ = lean_array_get_size(v_data_1960_);
v___x_1962_ = lean_unsigned_to_nat(2u);
v_nbuckets_1963_ = lean_nat_mul(v___x_1961_, v___x_1962_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_mk_array(v_nbuckets_1963_, v___x_1965_);
v___x_1967_ = lean_array_propagate_mark(v_data_1960_, v___x_1966_);
v___x_1968_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v___x_1964_, v_data_1960_, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(lean_object* v_m_1969_, lean_object* v_a_1970_, lean_object* v_b_1971_){
_start:
{
lean_object* v_size_1972_; lean_object* v_buckets_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2016_; 
v_size_1972_ = lean_ctor_get(v_m_1969_, 0);
v_buckets_1973_ = lean_ctor_get(v_m_1969_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_m_1969_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1975_ = v_m_1969_;
v_isShared_1976_ = v_isSharedCheck_2016_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_buckets_1973_);
lean_inc(v_size_1972_);
lean_dec(v_m_1969_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2016_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; uint64_t v___x_1978_; uint64_t v___x_1979_; uint64_t v___x_1980_; uint64_t v_fold_1981_; uint64_t v___x_1982_; uint64_t v___x_1983_; uint64_t v___x_1984_; size_t v___x_1985_; size_t v___x_1986_; size_t v___x_1987_; size_t v___x_1988_; size_t v___x_1989_; lean_object* v_bkt_1990_; uint8_t v___x_1991_; 
v___x_1977_ = lean_array_get_size(v_buckets_1973_);
v___x_1978_ = lean_uint64_of_nat(v_a_1970_);
v___x_1979_ = 32ULL;
v___x_1980_ = lean_uint64_shift_right(v___x_1978_, v___x_1979_);
v_fold_1981_ = lean_uint64_xor(v___x_1978_, v___x_1980_);
v___x_1982_ = 16ULL;
v___x_1983_ = lean_uint64_shift_right(v_fold_1981_, v___x_1982_);
v___x_1984_ = lean_uint64_xor(v_fold_1981_, v___x_1983_);
v___x_1985_ = lean_uint64_to_usize(v___x_1984_);
v___x_1986_ = lean_usize_of_nat(v___x_1977_);
v___x_1987_ = ((size_t)1ULL);
v___x_1988_ = lean_usize_sub(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_usize_land(v___x_1985_, v___x_1988_);
v_bkt_1990_ = lean_array_uget_borrowed(v_buckets_1973_, v___x_1989_);
v___x_1991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1970_, v_bkt_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v_size_x27_1993_; lean_object* v___x_1994_; lean_object* v_buckets_x27_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v_size_x27_1993_ = lean_nat_add(v_size_1972_, v___x_1992_);
lean_dec(v_size_1972_);
lean_inc(v_bkt_1990_);
v___x_1994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1994_, 0, v_a_1970_);
lean_ctor_set(v___x_1994_, 1, v_b_1971_);
lean_ctor_set(v___x_1994_, 2, v_bkt_1990_);
v_buckets_x27_1995_ = lean_array_uset(v_buckets_1973_, v___x_1989_, v___x_1994_);
v___x_1996_ = lean_unsigned_to_nat(4u);
v___x_1997_ = lean_nat_mul(v_size_x27_1993_, v___x_1996_);
v___x_1998_ = lean_unsigned_to_nat(3u);
v___x_1999_ = lean_nat_div(v___x_1997_, v___x_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_array_get_size(v_buckets_x27_1995_);
v___x_2001_ = lean_nat_dec_le(v___x_1999_, v___x_2000_);
lean_dec(v___x_1999_);
if (v___x_2001_ == 0)
{
lean_object* v_val_2002_; lean_object* v___x_2004_; 
v_val_2002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_buckets_x27_1995_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_val_2002_);
lean_ctor_set(v___x_1975_, 0, v_size_x27_1993_);
v___x_2004_ = v___x_1975_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_size_x27_1993_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_val_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
else
{
lean_object* v___x_2007_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_buckets_x27_1995_);
lean_ctor_set(v___x_1975_, 0, v_size_x27_1993_);
v___x_2007_ = v___x_1975_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_size_x27_1993_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_buckets_x27_1995_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v_buckets_x27_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_inc(v_bkt_1990_);
v___x_2009_ = lean_box(0);
v_buckets_x27_2010_ = lean_array_uset(v_buckets_1973_, v___x_1989_, v___x_2009_);
v___x_2011_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1970_, v_b_1971_, v_bkt_1990_);
v___x_2012_ = lean_array_uset(v_buckets_x27_2010_, v___x_1989_, v___x_2011_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v___x_2012_);
v___x_2014_ = v___x_1975_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_size_1972_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2));
v___x_2021_ = lean_unsigned_to_nat(48u);
v___x_2022_ = lean_unsigned_to_nat(370u);
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1));
v___x_2024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0));
v___x_2025_ = l_mkPanicMessageWithDecl(v___x_2024_, v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(lean_object* v_as_2026_, size_t v_sz_2027_, size_t v_i_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_a_2043_; uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_lt(v_i_2028_, v_sz_2027_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2029_);
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v_snd_2050_; lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2087_; 
v_a_2049_ = lean_array_uget_borrowed(v_as_2026_, v_i_2028_);
v_snd_2050_ = lean_ctor_get(v_a_2049_, 1);
v_fst_2051_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2052_ = lean_ctor_get(v_snd_2050_, 1);
v_fst_2053_ = lean_ctor_get(v_b_2029_, 0);
v_snd_2054_ = lean_ctor_get(v_b_2029_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_b_2029_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2056_ = v_b_2029_;
v_isShared_2057_ = v_isSharedCheck_2087_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
lean_dec(v_b_2029_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2087_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_fst_2051_, v___y_2031_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_object* v_val_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v_val_2060_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v_a_2059_, 1);
lean_inc_n(v_snd_2052_, 2);
v___x_2061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_snd_2054_, v_val_2060_, v_snd_2052_);
lean_inc(v_fst_2051_);
v___x_2062_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_fst_2053_, v_fst_2051_, v_snd_2052_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2061_);
lean_ctor_set(v___x_2056_, 0, v___x_2062_);
v___x_2064_ = v___x_2056_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2061_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_a_2043_ = v___x_2064_;
goto v___jp_2042_;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_dec(v_a_2059_);
v___x_2066_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3);
v___x_2067_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v___x_2066_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref_known(v___x_2067_, 1);
if (v_isShared_2057_ == 0)
{
v___x_2069_ = v___x_2056_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_fst_2053_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_snd_2054_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v_a_2043_ = v___x_2069_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2056_);
lean_dec(v_snd_2054_);
lean_dec(v_fst_2053_);
v_a_2071_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2067_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_2056_);
lean_dec(v_snd_2054_);
lean_dec(v_fst_2053_);
v_a_2079_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2058_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2058_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
v___jp_2042_:
{
size_t v___x_2044_; size_t v___x_2045_; 
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2028_, v___x_2044_);
v_i_2028_ = v___x_2045_;
v_b_2029_ = v_a_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___boxed(lean_object* v_as_2088_, lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
size_t v_sz_boxed_2104_; size_t v_i_boxed_2105_; lean_object* v_res_2106_; 
v_sz_boxed_2104_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2105_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_as_2088_, v_sz_boxed_2104_, v_i_boxed_2105_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_as_2088_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object* v_arr_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_exprCex_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_atomCex_2130_; lean_object* v___x_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_box(0);
v_exprCex_2122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1);
v___x_2123_ = lean_array_get_size(v_arr_2107_);
v___x_2124_ = lean_unsigned_to_nat(4u);
v___x_2125_ = lean_nat_mul(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_unsigned_to_nat(3u);
v___x_2127_ = lean_nat_div(v___x_2125_, v___x_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = l_Nat_nextPowerOfTwo(v___x_2127_);
lean_dec(v___x_2127_);
v___x_2129_ = lean_mk_array(v___x_2128_, v___x_2121_);
v_atomCex_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_atomCex_2130_, 0, v___x_2120_);
lean_ctor_set(v_atomCex_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_exprCex_2122_);
lean_ctor_set(v___x_2131_, 1, v_atomCex_2130_);
v_sz_2132_ = lean_array_size(v_arr_2107_);
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_arr_2107_, v_sz_2132_, v___x_2133_, v___x_2131_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2151_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2151_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2151_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_fst_2139_; lean_object* v_snd_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2150_; 
v_fst_2139_ = lean_ctor_get(v_a_2135_, 0);
v_snd_2140_ = lean_ctor_get(v_a_2135_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2135_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2142_ = v_a_2135_;
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_snd_2140_);
lean_inc(v_fst_2139_);
lean_dec(v_a_2135_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_fst_2139_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2140_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2145_);
v___x_2147_ = v___x_2137_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2134_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2134_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object* v_arr_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_arr_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec_ref(v_arr_2160_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0(lean_object* v_00_u03b2_2174_, lean_object* v_m_2175_, lean_object* v_a_2176_, lean_object* v_b_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_m_2175_, v_a_2176_, v_b_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1(lean_object* v_00_u03b2_2179_, lean_object* v_m_2180_, lean_object* v_a_2181_, lean_object* v_b_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_m_2180_, v_a_2181_, v_b_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_object* v_00_u03b2_2184_, lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_2185_, v_x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2188_, lean_object* v_a_2189_, lean_object* v_x_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(v_00_u03b2_2188_, v_a_2189_, v_x_2190_);
lean_dec(v_x_2190_);
lean_dec(v_a_2189_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1(lean_object* v_00_u03b2_2193_, lean_object* v_data_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_data_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2(lean_object* v_00_u03b2_2196_, lean_object* v_a_2197_, lean_object* v_b_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_2197_, v_b_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_object* v_00_u03b2_2201_, lean_object* v_a_2202_, lean_object* v_x_2203_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_2202_, v_x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2205_, lean_object* v_a_2206_, lean_object* v_x_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(v_00_u03b2_2205_, v_a_2206_, v_x_2207_);
lean_dec(v_x_2207_);
lean_dec_ref(v_a_2206_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5(lean_object* v_00_u03b2_2210_, lean_object* v_data_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_data_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6(lean_object* v_00_u03b2_2213_, lean_object* v_a_2214_, lean_object* v_b_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_2214_, v_b_2215_, v_x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2218_, lean_object* v_i_2219_, lean_object* v_source_2220_, lean_object* v_target_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v_i_2219_, v_source_2220_, v_target_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8(lean_object* v_00_u03b2_2223_, lean_object* v_i_2224_, lean_object* v_source_2225_, lean_object* v_target_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v_i_2224_, v_source_2225_, v_target_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2229_, v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object* v_cert_2240_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_cert_2240_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object* v_cert_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v_usedHyps_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2247_ = lean_st_ref_get(v_a_2245_);
v_usedHyps_2248_ = lean_ctor_get(v___x_2247_, 2);
lean_inc_ref(v_usedHyps_2248_);
lean_dec(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_usedHyps_2248_);
lean_ctor_set(v___x_2249_, 1, v_cert_2244_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg___boxed(lean_object* v_cert_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_2251_, v_a_2252_);
lean_dec(v_a_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(lean_object* v_cert_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_2255_, v_a_2257_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___boxed(lean_object* v_cert_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(v_cert_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2288_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Cadical_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Cadical_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default);
l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry);
l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default);
l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel);
l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0 = _init_l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0();
lean_mark_persistent(l_Std_Internal_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* initialize_Lean_Cadical_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Cadical_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_InstSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
