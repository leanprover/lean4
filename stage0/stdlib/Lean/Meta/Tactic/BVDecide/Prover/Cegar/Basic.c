// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Basic public import Lean.Meta.Tactic.BVDecide.TacticContext public import Lean.Cadical.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Std_Sat_AIG_empty___redArg();
lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Cadical_Solver_new();
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_array_object l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1___boxed(lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6;
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
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_unsigned_to_nat(16u);
v___x_23_ = lean_mk_array(v___x_22_, v___x_21_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2);
v___x_28_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0));
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(lean_object* v_aig_31_){
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1___boxed(lean_object* v_aig_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_37_);
lean_dec_ref(v_aig_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(lean_object* v_aig_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0));
v___x_43_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_41_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___boxed(lean_object* v_aig_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v_aig_45_);
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
v___x_51_ = l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_52_ = l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2);
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_55_ = l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_53_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5);
v___x_61_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
lean_ctor_set(v___x_61_, 2, v___x_60_);
lean_ctor_set(v___x_61_, 3, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new(){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_63_ = l_Lean_Cadical_Solver_new();
v___x_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_65_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3);
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v___x_67_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_66_);
lean_ctor_set(v___x_67_, 3, v___x_63_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_satExpr_74_; lean_object* v_unusedHypotheses_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_st_ref_get(v_a_71_);
v_satExpr_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_satExpr_74_);
lean_dec(v___x_73_);
v_unusedHypotheses_75_ = lean_ctor_get(v_a_70_, 1);
lean_inc_ref(v_unusedHypotheses_75_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_satExpr_74_);
lean_ctor_set(v___x_76_, 1, v_unusedHypotheses_75_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_82_, v_a_83_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___boxed(lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; uint8_t v_didChange_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_st_ref_get(v_a_114_);
v_didChange_117_ = lean_ctor_get_uint8(v___x_116_, sizeof(void*)*6);
lean_dec(v___x_116_);
v___x_118_ = lean_box(v_didChange_117_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg___boxed(lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(v_a_120_);
lean_dec(v_a_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; uint8_t v_didChange_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_138_ = lean_st_ref_get(v_a_124_);
v_didChange_139_ = lean_ctor_get_uint8(v___x_138_, sizeof(void*)*6);
lean_dec(v___x_138_);
v___x_140_ = lean_box(v_didChange_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___boxed(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(uint8_t v_v_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_satExpr_162_; lean_object* v_hypQueue_163_; lean_object* v_usedHyps_164_; lean_object* v_theoryState_165_; lean_object* v_solverTimeBudgetMs_166_; lean_object* v_roundBudget_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_177_; 
v___x_161_ = lean_st_ref_take(v_a_159_);
v_satExpr_162_ = lean_ctor_get(v___x_161_, 0);
v_hypQueue_163_ = lean_ctor_get(v___x_161_, 1);
v_usedHyps_164_ = lean_ctor_get(v___x_161_, 2);
v_theoryState_165_ = lean_ctor_get(v___x_161_, 3);
v_solverTimeBudgetMs_166_ = lean_ctor_get(v___x_161_, 4);
v_roundBudget_167_ = lean_ctor_get(v___x_161_, 5);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_177_ == 0)
{
v___x_169_ = v___x_161_;
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_roundBudget_167_);
lean_inc(v_solverTimeBudgetMs_166_);
lean_inc(v_theoryState_165_);
lean_inc(v_usedHyps_164_);
lean_inc(v_hypQueue_163_);
lean_inc(v_satExpr_162_);
lean_dec(v___x_161_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_171_ = lean_box(0);
if (v_isShared_170_ == 0)
{
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_satExpr_162_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_hypQueue_163_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_usedHyps_164_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_theoryState_165_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_solverTimeBudgetMs_166_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v_roundBudget_167_);
v___x_173_ = v_reuseFailAlloc_176_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*6, v_v_158_);
v___x_174_ = lean_st_ref_put(v_a_159_, v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_171_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg___boxed(lean_object* v_v_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_v_boxed_181_; lean_object* v_res_182_; 
v_v_boxed_181_ = lean_unbox(v_v_178_);
v_res_182_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(v_v_boxed_181_, v_a_179_);
lean_dec(v_a_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(uint8_t v_v_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_satExpr_200_; lean_object* v_hypQueue_201_; lean_object* v_usedHyps_202_; lean_object* v_theoryState_203_; lean_object* v_solverTimeBudgetMs_204_; lean_object* v_roundBudget_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_215_; 
v___x_199_ = lean_st_ref_take(v_a_185_);
v_satExpr_200_ = lean_ctor_get(v___x_199_, 0);
v_hypQueue_201_ = lean_ctor_get(v___x_199_, 1);
v_usedHyps_202_ = lean_ctor_get(v___x_199_, 2);
v_theoryState_203_ = lean_ctor_get(v___x_199_, 3);
v_solverTimeBudgetMs_204_ = lean_ctor_get(v___x_199_, 4);
v_roundBudget_205_ = lean_ctor_get(v___x_199_, 5);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_215_ == 0)
{
v___x_207_ = v___x_199_;
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_roundBudget_205_);
lean_inc(v_solverTimeBudgetMs_204_);
lean_inc(v_theoryState_203_);
lean_inc(v_usedHyps_202_);
lean_inc(v_hypQueue_201_);
lean_inc(v_satExpr_200_);
lean_dec(v___x_199_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_box(0);
if (v_isShared_208_ == 0)
{
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_satExpr_200_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_hypQueue_201_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_usedHyps_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_theoryState_203_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_solverTimeBudgetMs_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 5, v_roundBudget_205_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*6, v_v_183_);
v___x_212_ = lean_st_ref_put(v_a_185_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_209_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___boxed(lean_object* v_v_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
uint8_t v_v_boxed_232_; lean_object* v_res_233_; 
v_v_boxed_232_ = lean_unbox(v_v_216_);
v_res_233_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(v_v_boxed_232_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; lean_object* v_theoryState_237_; lean_object* v___x_238_; 
v___x_236_ = lean_st_ref_get(v_a_234_);
v_theoryState_237_ = lean_ctor_get(v___x_236_, 3);
lean_inc_ref(v_theoryState_237_);
lean_dec(v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_theoryState_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg___boxed(lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(v_a_239_);
lean_dec(v_a_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_theoryState_258_; lean_object* v___x_259_; 
v___x_257_ = lean_st_ref_get(v_a_243_);
v_theoryState_258_ = lean_ctor_get(v___x_257_, 3);
lean_inc_ref(v_theoryState_258_);
lean_dec(v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_theoryState_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(lean_object* v_f_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; lean_object* v_satExpr_280_; lean_object* v_hypQueue_281_; lean_object* v_usedHyps_282_; uint8_t v_didChange_283_; lean_object* v_theoryState_284_; lean_object* v_solverTimeBudgetMs_285_; lean_object* v_roundBudget_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_297_; 
v___x_279_ = lean_st_ref_take(v_a_277_);
v_satExpr_280_ = lean_ctor_get(v___x_279_, 0);
v_hypQueue_281_ = lean_ctor_get(v___x_279_, 1);
v_usedHyps_282_ = lean_ctor_get(v___x_279_, 2);
v_didChange_283_ = lean_ctor_get_uint8(v___x_279_, sizeof(void*)*6);
v_theoryState_284_ = lean_ctor_get(v___x_279_, 3);
v_solverTimeBudgetMs_285_ = lean_ctor_get(v___x_279_, 4);
v_roundBudget_286_ = lean_ctor_get(v___x_279_, 5);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_297_ == 0)
{
v___x_288_ = v___x_279_;
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_roundBudget_286_);
lean_inc(v_solverTimeBudgetMs_285_);
lean_inc(v_theoryState_284_);
lean_inc(v_usedHyps_282_);
lean_inc(v_hypQueue_281_);
lean_inc(v_satExpr_280_);
lean_dec(v___x_279_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = lean_box(0);
v___x_291_ = lean_apply_1(v_f_276_, v_theoryState_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_satExpr_280_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_hypQueue_281_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_usedHyps_282_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_solverTimeBudgetMs_285_);
lean_ctor_set(v_reuseFailAlloc_296_, 5, v_roundBudget_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_296_, sizeof(void*)*6, v_didChange_283_);
v___x_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_st_ref_put(v_a_277_, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_290_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg___boxed(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(v_f_298_, v_a_299_);
lean_dec(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(lean_object* v_f_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; lean_object* v_satExpr_319_; lean_object* v_hypQueue_320_; lean_object* v_usedHyps_321_; uint8_t v_didChange_322_; lean_object* v_theoryState_323_; lean_object* v_solverTimeBudgetMs_324_; lean_object* v_roundBudget_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_336_; 
v___x_318_ = lean_st_ref_take(v_a_304_);
v_satExpr_319_ = lean_ctor_get(v___x_318_, 0);
v_hypQueue_320_ = lean_ctor_get(v___x_318_, 1);
v_usedHyps_321_ = lean_ctor_get(v___x_318_, 2);
v_didChange_322_ = lean_ctor_get_uint8(v___x_318_, sizeof(void*)*6);
v_theoryState_323_ = lean_ctor_get(v___x_318_, 3);
v_solverTimeBudgetMs_324_ = lean_ctor_get(v___x_318_, 4);
v_roundBudget_325_ = lean_ctor_get(v___x_318_, 5);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_336_ == 0)
{
v___x_327_ = v___x_318_;
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_roundBudget_325_);
lean_inc(v_solverTimeBudgetMs_324_);
lean_inc(v_theoryState_323_);
lean_inc(v_usedHyps_321_);
lean_inc(v_hypQueue_320_);
lean_inc(v_satExpr_319_);
lean_dec(v___x_318_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_336_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_f_302_, v_theoryState_323_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 3, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_satExpr_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_hypQueue_320_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_usedHyps_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_solverTimeBudgetMs_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v_roundBudget_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*6, v_didChange_322_);
v___x_332_ = v_reuseFailAlloc_335_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_st_ref_put(v_a_304_, v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_329_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___boxed(lean_object* v_f_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(v_f_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_Sat_AIG_empty___redArg();
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_356_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1);
v___x_358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_359_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_358_);
lean_ctor_set(v___x_360_, 2, v___x_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_satExpr_364_; lean_object* v_hypQueue_365_; lean_object* v_usedHyps_366_; uint8_t v_didChange_367_; lean_object* v_theoryState_368_; lean_object* v_solverTimeBudgetMs_369_; lean_object* v_roundBudget_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_394_; 
v___x_363_ = lean_st_ref_take(v_a_361_);
v_satExpr_364_ = lean_ctor_get(v___x_363_, 0);
v_hypQueue_365_ = lean_ctor_get(v___x_363_, 1);
v_usedHyps_366_ = lean_ctor_get(v___x_363_, 2);
v_didChange_367_ = lean_ctor_get_uint8(v___x_363_, sizeof(void*)*6);
v_theoryState_368_ = lean_ctor_get(v___x_363_, 3);
v_solverTimeBudgetMs_369_ = lean_ctor_get(v___x_363_, 4);
v_roundBudget_370_ = lean_ctor_get(v___x_363_, 5);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_394_ == 0)
{
v___x_372_ = v___x_363_;
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_roundBudget_370_);
lean_inc(v_solverTimeBudgetMs_369_);
lean_inc(v_theoryState_368_);
lean_inc(v_usedHyps_366_);
lean_inc(v_hypQueue_365_);
lean_inc(v_satExpr_364_);
lean_dec(v___x_363_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_394_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v_satSolver_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_390_; 
v___x_374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_375_ = lean_ctor_get(v_theoryState_368_, 3);
v_isSharedCheck_390_ = !lean_is_exclusive(v_theoryState_368_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; lean_object* v_unused_392_; lean_object* v_unused_393_; 
v_unused_391_ = lean_ctor_get(v_theoryState_368_, 2);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v_theoryState_368_, 1);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_theoryState_368_, 0);
lean_dec(v_unused_393_);
v___x_377_ = v_theoryState_368_;
v_isShared_378_ = v_isSharedCheck_390_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_satSolver_375_);
lean_dec(v_theoryState_368_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_390_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_381_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 2, v___x_374_);
lean_ctor_set(v___x_377_, 1, v___x_381_);
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_383_ = v___x_377_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_389_, 3, v_satSolver_375_);
v___x_383_ = v_reuseFailAlloc_389_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_385_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 3, v___x_383_);
v___x_385_ = v___x_372_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_satExpr_364_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_hypQueue_365_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_usedHyps_366_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_solverTimeBudgetMs_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_roundBudget_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_388_, sizeof(void*)*6, v_didChange_367_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_st_ref_put(v_a_361_, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_379_);
return v___x_387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___boxed(lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(v_a_395_);
lean_dec(v_a_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_satExpr_414_; lean_object* v_hypQueue_415_; lean_object* v_usedHyps_416_; uint8_t v_didChange_417_; lean_object* v_theoryState_418_; lean_object* v_solverTimeBudgetMs_419_; lean_object* v_roundBudget_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_444_; 
v___x_413_ = lean_st_ref_take(v_a_399_);
v_satExpr_414_ = lean_ctor_get(v___x_413_, 0);
v_hypQueue_415_ = lean_ctor_get(v___x_413_, 1);
v_usedHyps_416_ = lean_ctor_get(v___x_413_, 2);
v_didChange_417_ = lean_ctor_get_uint8(v___x_413_, sizeof(void*)*6);
v_theoryState_418_ = lean_ctor_get(v___x_413_, 3);
v_solverTimeBudgetMs_419_ = lean_ctor_get(v___x_413_, 4);
v_roundBudget_420_ = lean_ctor_get(v___x_413_, 5);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_444_ == 0)
{
v___x_422_ = v___x_413_;
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_roundBudget_420_);
lean_inc(v_solverTimeBudgetMs_419_);
lean_inc(v_theoryState_418_);
lean_inc(v_usedHyps_416_);
lean_inc(v_hypQueue_415_);
lean_inc(v_satExpr_414_);
lean_dec(v___x_413_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_satSolver_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_440_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_425_ = lean_ctor_get(v_theoryState_418_, 3);
v_isSharedCheck_440_ = !lean_is_exclusive(v_theoryState_418_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_441_ = lean_ctor_get(v_theoryState_418_, 2);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_theoryState_418_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_theoryState_418_, 0);
lean_dec(v_unused_443_);
v___x_427_ = v_theoryState_418_;
v_isShared_428_ = v_isSharedCheck_440_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_satSolver_425_);
lean_dec(v_theoryState_418_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_440_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_431_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 2, v___x_424_);
lean_ctor_set(v___x_427_, 1, v___x_431_);
lean_ctor_set(v___x_427_, 0, v___x_430_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_satSolver_425_);
v___x_433_ = v_reuseFailAlloc_439_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 3, v___x_433_);
v___x_435_ = v___x_422_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_satExpr_414_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_hypQueue_415_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_usedHyps_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_solverTimeBudgetMs_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_roundBudget_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*6, v_didChange_417_);
v___x_435_ = v_reuseFailAlloc_438_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_st_ref_put(v_a_399_, v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_429_);
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___boxed(lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(lean_object* v_hyp_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_satExpr_465_; lean_object* v_hypQueue_466_; lean_object* v_usedHyps_467_; uint8_t v_didChange_468_; lean_object* v_theoryState_469_; lean_object* v_solverTimeBudgetMs_470_; lean_object* v_roundBudget_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_482_; 
v___x_464_ = lean_st_ref_take(v_a_462_);
v_satExpr_465_ = lean_ctor_get(v___x_464_, 0);
v_hypQueue_466_ = lean_ctor_get(v___x_464_, 1);
v_usedHyps_467_ = lean_ctor_get(v___x_464_, 2);
v_didChange_468_ = lean_ctor_get_uint8(v___x_464_, sizeof(void*)*6);
v_theoryState_469_ = lean_ctor_get(v___x_464_, 3);
v_solverTimeBudgetMs_470_ = lean_ctor_get(v___x_464_, 4);
v_roundBudget_471_ = lean_ctor_get(v___x_464_, 5);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_482_ == 0)
{
v___x_473_ = v___x_464_;
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_roundBudget_471_);
lean_inc(v_solverTimeBudgetMs_470_);
lean_inc(v_theoryState_469_);
lean_inc(v_usedHyps_467_);
lean_inc(v_hypQueue_466_);
lean_inc(v_satExpr_465_);
lean_dec(v___x_464_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_482_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_array_push(v_hypQueue_466_, v_hyp_461_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_476_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_satExpr_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_usedHyps_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_theoryState_469_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_solverTimeBudgetMs_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_roundBudget_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*6, v_didChange_468_);
v___x_478_ = v_reuseFailAlloc_481_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_st_ref_put(v_a_462_, v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_475_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg___boxed(lean_object* v_hyp_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(v_hyp_483_, v_a_484_);
lean_dec(v_a_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(lean_object* v_hyp_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_satExpr_504_; lean_object* v_hypQueue_505_; lean_object* v_usedHyps_506_; uint8_t v_didChange_507_; lean_object* v_theoryState_508_; lean_object* v_solverTimeBudgetMs_509_; lean_object* v_roundBudget_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_521_; 
v___x_503_ = lean_st_ref_take(v_a_489_);
v_satExpr_504_ = lean_ctor_get(v___x_503_, 0);
v_hypQueue_505_ = lean_ctor_get(v___x_503_, 1);
v_usedHyps_506_ = lean_ctor_get(v___x_503_, 2);
v_didChange_507_ = lean_ctor_get_uint8(v___x_503_, sizeof(void*)*6);
v_theoryState_508_ = lean_ctor_get(v___x_503_, 3);
v_solverTimeBudgetMs_509_ = lean_ctor_get(v___x_503_, 4);
v_roundBudget_510_ = lean_ctor_get(v___x_503_, 5);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_512_ = v___x_503_;
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_roundBudget_510_);
lean_inc(v_solverTimeBudgetMs_509_);
lean_inc(v_theoryState_508_);
lean_inc(v_usedHyps_506_);
lean_inc(v_hypQueue_505_);
lean_inc(v_satExpr_504_);
lean_dec(v___x_503_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_array_push(v_hypQueue_505_, v_hyp_487_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_satExpr_504_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_usedHyps_506_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_theoryState_508_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v_solverTimeBudgetMs_509_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v_roundBudget_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_520_, sizeof(void*)*6, v_didChange_507_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_st_ref_put(v_a_489_, v___x_517_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_514_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___boxed(lean_object* v_hyp_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(v_hyp_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_usedHyps_542_; lean_object* v___x_543_; 
v___x_541_ = lean_st_ref_get(v_a_539_);
v_usedHyps_542_ = lean_ctor_get(v___x_541_, 2);
lean_inc_ref(v_usedHyps_542_);
lean_dec(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_usedHyps_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg___boxed(lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(v_a_544_);
lean_dec(v_a_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_usedHyps_563_; lean_object* v___x_564_; 
v___x_562_ = lean_st_ref_get(v_a_548_);
v_usedHyps_563_ = lean_ctor_get(v___x_562_, 2);
lean_inc_ref(v_usedHyps_563_);
lean_dec(v___x_562_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v_usedHyps_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___boxed(lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_satExpr_586_; lean_object* v_hypQueue_587_; lean_object* v_usedHyps_588_; uint8_t v_didChange_589_; lean_object* v_theoryState_590_; lean_object* v_solverTimeBudgetMs_591_; lean_object* v_roundBudget_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_603_; 
v___x_585_ = lean_st_ref_take(v_a_583_);
v_satExpr_586_ = lean_ctor_get(v___x_585_, 0);
v_hypQueue_587_ = lean_ctor_get(v___x_585_, 1);
v_usedHyps_588_ = lean_ctor_get(v___x_585_, 2);
v_didChange_589_ = lean_ctor_get_uint8(v___x_585_, sizeof(void*)*6);
v_theoryState_590_ = lean_ctor_get(v___x_585_, 3);
v_solverTimeBudgetMs_591_ = lean_ctor_get(v___x_585_, 4);
v_roundBudget_592_ = lean_ctor_get(v___x_585_, 5);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_603_ == 0)
{
v___x_594_ = v___x_585_;
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_roundBudget_592_);
lean_inc(v_solverTimeBudgetMs_591_);
lean_inc(v_theoryState_590_);
lean_inc(v_usedHyps_588_);
lean_inc(v_hypQueue_587_);
lean_inc(v_satExpr_586_);
lean_dec(v___x_585_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_603_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_597_ = l_Array_append___redArg(v_usedHyps_588_, v_hypQueue_587_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 2, v___x_597_);
lean_ctor_set(v___x_594_, 1, v___x_596_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_satExpr_586_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_theoryState_590_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_solverTimeBudgetMs_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 5, v_roundBudget_592_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*6, v_didChange_589_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_st_ref_put(v_a_583_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_hypQueue_587_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___boxed(lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(v_a_604_);
lean_dec(v_a_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_satExpr_623_; lean_object* v_hypQueue_624_; lean_object* v_usedHyps_625_; uint8_t v_didChange_626_; lean_object* v_theoryState_627_; lean_object* v_solverTimeBudgetMs_628_; lean_object* v_roundBudget_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_640_; 
v___x_622_ = lean_st_ref_take(v_a_608_);
v_satExpr_623_ = lean_ctor_get(v___x_622_, 0);
v_hypQueue_624_ = lean_ctor_get(v___x_622_, 1);
v_usedHyps_625_ = lean_ctor_get(v___x_622_, 2);
v_didChange_626_ = lean_ctor_get_uint8(v___x_622_, sizeof(void*)*6);
v_theoryState_627_ = lean_ctor_get(v___x_622_, 3);
v_solverTimeBudgetMs_628_ = lean_ctor_get(v___x_622_, 4);
v_roundBudget_629_ = lean_ctor_get(v___x_622_, 5);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_640_ == 0)
{
v___x_631_ = v___x_622_;
v_isShared_632_ = v_isSharedCheck_640_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_roundBudget_629_);
lean_inc(v_solverTimeBudgetMs_628_);
lean_inc(v_theoryState_627_);
lean_inc(v_usedHyps_625_);
lean_inc(v_hypQueue_624_);
lean_inc(v_satExpr_623_);
lean_dec(v___x_622_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_640_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_634_ = l_Array_append___redArg(v_usedHyps_625_, v_hypQueue_624_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 2, v___x_634_);
lean_ctor_set(v___x_631_, 1, v___x_633_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_satExpr_623_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_theoryState_627_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_solverTimeBudgetMs_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 5, v_roundBudget_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, sizeof(void*)*6, v_didChange_626_);
v___x_636_ = v_reuseFailAlloc_639_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_st_ref_put(v_a_608_, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_hypQueue_624_);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___boxed(lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(lean_object* v_a_657_){
_start:
{
lean_object* v_tacticContext_659_; lean_object* v___x_660_; 
v_tacticContext_659_ = lean_ctor_get(v_a_657_, 2);
lean_inc_ref(v_tacticContext_659_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_tacticContext_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg___boxed(lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(v_a_661_);
lean_dec_ref(v_a_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_tacticContext_679_; lean_object* v___x_680_; 
v_tacticContext_679_ = lean_ctor_get(v_a_664_, 2);
lean_inc_ref(v_tacticContext_679_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_tacticContext_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___boxed(lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(lean_object* v_a_697_){
_start:
{
lean_object* v_tacticContext_699_; lean_object* v_config_700_; uint8_t v_uf_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_tacticContext_699_ = lean_ctor_get(v_a_697_, 2);
v_config_700_ = lean_ctor_get(v_tacticContext_699_, 5);
v_uf_701_ = lean_ctor_get_uint8(v_config_700_, sizeof(void*)*3 + 11);
v___x_702_ = lean_box(v_uf_701_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg___boxed(lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(v_a_704_);
lean_dec_ref(v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_tacticContext_722_; lean_object* v_config_723_; uint8_t v_uf_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_tacticContext_722_ = lean_ctor_get(v_a_707_, 2);
v_config_723_ = lean_ctor_get(v_tacticContext_722_, 5);
v_uf_724_ = lean_ctor_get_uint8(v_config_723_, sizeof(void*)*3 + 11);
v___x_725_ = lean_box(v_uf_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___boxed(lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(lean_object* v_ms_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_746_; lean_object* v_satExpr_747_; lean_object* v_hypQueue_748_; lean_object* v_usedHyps_749_; uint8_t v_didChange_750_; lean_object* v_theoryState_751_; lean_object* v_solverTimeBudgetMs_752_; lean_object* v_roundBudget_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v___x_746_ = lean_st_ref_take(v_a_744_);
v_satExpr_747_ = lean_ctor_get(v___x_746_, 0);
v_hypQueue_748_ = lean_ctor_get(v___x_746_, 1);
v_usedHyps_749_ = lean_ctor_get(v___x_746_, 2);
v_didChange_750_ = lean_ctor_get_uint8(v___x_746_, sizeof(void*)*6);
v_theoryState_751_ = lean_ctor_get(v___x_746_, 3);
v_solverTimeBudgetMs_752_ = lean_ctor_get(v___x_746_, 4);
v_roundBudget_753_ = lean_ctor_get(v___x_746_, 5);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v___x_746_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_roundBudget_753_);
lean_inc(v_solverTimeBudgetMs_752_);
lean_inc(v_theoryState_751_);
lean_inc(v_usedHyps_749_);
lean_inc(v_hypQueue_748_);
lean_inc(v_satExpr_747_);
lean_dec(v___x_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_box(0);
v___x_758_ = lean_nat_sub(v_solverTimeBudgetMs_752_, v_ms_743_);
lean_dec(v_solverTimeBudgetMs_752_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 4, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_satExpr_747_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_hypQueue_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_usedHyps_749_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_theoryState_751_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_roundBudget_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*6, v_didChange_750_);
v___x_760_ = v_reuseFailAlloc_763_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_st_ref_put(v_a_744_, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_757_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg___boxed(lean_object* v_ms_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(v_ms_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec(v_ms_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(lean_object* v_ms_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_satExpr_786_; lean_object* v_hypQueue_787_; lean_object* v_usedHyps_788_; uint8_t v_didChange_789_; lean_object* v_theoryState_790_; lean_object* v_solverTimeBudgetMs_791_; lean_object* v_roundBudget_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_803_; 
v___x_785_ = lean_st_ref_take(v_a_771_);
v_satExpr_786_ = lean_ctor_get(v___x_785_, 0);
v_hypQueue_787_ = lean_ctor_get(v___x_785_, 1);
v_usedHyps_788_ = lean_ctor_get(v___x_785_, 2);
v_didChange_789_ = lean_ctor_get_uint8(v___x_785_, sizeof(void*)*6);
v_theoryState_790_ = lean_ctor_get(v___x_785_, 3);
v_solverTimeBudgetMs_791_ = lean_ctor_get(v___x_785_, 4);
v_roundBudget_792_ = lean_ctor_get(v___x_785_, 5);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_803_ == 0)
{
v___x_794_ = v___x_785_;
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_roundBudget_792_);
lean_inc(v_solverTimeBudgetMs_791_);
lean_inc(v_theoryState_790_);
lean_inc(v_usedHyps_788_);
lean_inc(v_hypQueue_787_);
lean_inc(v_satExpr_786_);
lean_dec(v___x_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_box(0);
v___x_797_ = lean_nat_sub(v_solverTimeBudgetMs_791_, v_ms_769_);
lean_dec(v_solverTimeBudgetMs_791_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 4, v___x_797_);
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_satExpr_786_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_hypQueue_787_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_usedHyps_788_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_theoryState_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v_roundBudget_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_802_, sizeof(void*)*6, v_didChange_789_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_st_ref_put(v_a_771_, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_796_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___boxed(lean_object* v_ms_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(v_ms_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_ms_804_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_solverTimeBudgetMs_824_; lean_object* v___x_825_; 
v___x_823_ = lean_st_ref_get(v_a_821_);
v_solverTimeBudgetMs_824_ = lean_ctor_get(v___x_823_, 4);
lean_inc(v_solverTimeBudgetMs_824_);
lean_dec(v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_solverTimeBudgetMs_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg___boxed(lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(v_a_826_);
lean_dec(v_a_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_solverTimeBudgetMs_845_; lean_object* v___x_846_; 
v___x_844_ = lean_st_ref_get(v_a_830_);
v_solverTimeBudgetMs_845_ = lean_ctor_get(v___x_844_, 4);
lean_inc(v_solverTimeBudgetMs_845_);
lean_dec(v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_solverTimeBudgetMs_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___boxed(lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v_satExpr_866_; lean_object* v_hypQueue_867_; lean_object* v_usedHyps_868_; uint8_t v_didChange_869_; lean_object* v_theoryState_870_; lean_object* v_solverTimeBudgetMs_871_; lean_object* v_roundBudget_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_884_; 
v___x_865_ = lean_st_ref_take(v_a_863_);
v_satExpr_866_ = lean_ctor_get(v___x_865_, 0);
v_hypQueue_867_ = lean_ctor_get(v___x_865_, 1);
v_usedHyps_868_ = lean_ctor_get(v___x_865_, 2);
v_didChange_869_ = lean_ctor_get_uint8(v___x_865_, sizeof(void*)*6);
v_theoryState_870_ = lean_ctor_get(v___x_865_, 3);
v_solverTimeBudgetMs_871_ = lean_ctor_get(v___x_865_, 4);
v_roundBudget_872_ = lean_ctor_get(v___x_865_, 5);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_884_ == 0)
{
v___x_874_ = v___x_865_;
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_roundBudget_872_);
lean_inc(v_solverTimeBudgetMs_871_);
lean_inc(v_theoryState_870_);
lean_inc(v_usedHyps_868_);
lean_inc(v_hypQueue_867_);
lean_inc(v_satExpr_866_);
lean_dec(v___x_865_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_876_ = lean_box(0);
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_sub(v_roundBudget_872_, v___x_877_);
lean_dec(v_roundBudget_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 5, v___x_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_satExpr_866_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_hypQueue_867_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_usedHyps_868_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_theoryState_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_solverTimeBudgetMs_871_);
lean_ctor_set(v_reuseFailAlloc_883_, 5, v___x_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*6, v_didChange_869_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_st_ref_put(v_a_863_, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_876_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg___boxed(lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(v_a_885_);
lean_dec(v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v_satExpr_904_; lean_object* v_hypQueue_905_; lean_object* v_usedHyps_906_; uint8_t v_didChange_907_; lean_object* v_theoryState_908_; lean_object* v_solverTimeBudgetMs_909_; lean_object* v_roundBudget_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v___x_903_ = lean_st_ref_take(v_a_889_);
v_satExpr_904_ = lean_ctor_get(v___x_903_, 0);
v_hypQueue_905_ = lean_ctor_get(v___x_903_, 1);
v_usedHyps_906_ = lean_ctor_get(v___x_903_, 2);
v_didChange_907_ = lean_ctor_get_uint8(v___x_903_, sizeof(void*)*6);
v_theoryState_908_ = lean_ctor_get(v___x_903_, 3);
v_solverTimeBudgetMs_909_ = lean_ctor_get(v___x_903_, 4);
v_roundBudget_910_ = lean_ctor_get(v___x_903_, 5);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v___x_903_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_roundBudget_910_);
lean_inc(v_solverTimeBudgetMs_909_);
lean_inc(v_theoryState_908_);
lean_inc(v_usedHyps_906_);
lean_inc(v_hypQueue_905_);
lean_inc(v_satExpr_904_);
lean_dec(v___x_903_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_sub(v_roundBudget_910_, v___x_915_);
lean_dec(v_roundBudget_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 5, v___x_916_);
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_satExpr_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_hypQueue_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_usedHyps_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_theoryState_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_solverTimeBudgetMs_909_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v___x_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*6, v_didChange_907_);
v___x_918_ = v_reuseFailAlloc_921_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_st_ref_put(v_a_889_, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_914_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___boxed(lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_roundBudget_942_; lean_object* v___x_943_; 
v___x_941_ = lean_st_ref_get(v_a_939_);
v_roundBudget_942_ = lean_ctor_get(v___x_941_, 5);
lean_inc(v_roundBudget_942_);
lean_dec(v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_roundBudget_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg___boxed(lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(v_a_944_);
lean_dec(v_a_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_roundBudget_963_; lean_object* v___x_964_; 
v___x_962_ = lean_st_ref_get(v_a_948_);
v_roundBudget_963_ = lean_ctor_get(v___x_962_, 5);
lean_inc(v_roundBudget_963_);
lean_dec(v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_roundBudget_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___boxed(lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(lean_object* v_a_981_){
_start:
{
lean_object* v___x_983_; lean_object* v_theoryState_984_; lean_object* v_satExpr_985_; lean_object* v_hypQueue_986_; lean_object* v_usedHyps_987_; uint8_t v_didChange_988_; lean_object* v_solverTimeBudgetMs_989_; lean_object* v_roundBudget_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1011_; 
v___x_983_ = lean_st_ref_take(v_a_981_);
v_theoryState_984_ = lean_ctor_get(v___x_983_, 3);
v_satExpr_985_ = lean_ctor_get(v___x_983_, 0);
v_hypQueue_986_ = lean_ctor_get(v___x_983_, 1);
v_usedHyps_987_ = lean_ctor_get(v___x_983_, 2);
v_didChange_988_ = lean_ctor_get_uint8(v___x_983_, sizeof(void*)*6);
v_solverTimeBudgetMs_989_ = lean_ctor_get(v___x_983_, 4);
v_roundBudget_990_ = lean_ctor_get(v___x_983_, 5);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_992_ = v___x_983_;
v_isShared_993_ = v_isSharedCheck_1011_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_roundBudget_990_);
lean_inc(v_solverTimeBudgetMs_989_);
lean_inc(v_theoryState_984_);
lean_inc(v_usedHyps_987_);
lean_inc(v_hypQueue_986_);
lean_inc(v_satExpr_985_);
lean_dec(v___x_983_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1011_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_funState_994_; lean_object* v_bitvecState_995_; lean_object* v_preprocessCaches_996_; lean_object* v_satSolver_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1010_; 
v_funState_994_ = lean_ctor_get(v_theoryState_984_, 0);
v_bitvecState_995_ = lean_ctor_get(v_theoryState_984_, 1);
v_preprocessCaches_996_ = lean_ctor_get(v_theoryState_984_, 2);
v_satSolver_997_ = lean_ctor_get(v_theoryState_984_, 3);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_theoryState_984_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_999_ = v_theoryState_984_;
v_isShared_1000_ = v_isSharedCheck_1010_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_satSolver_997_);
lean_inc(v_preprocessCaches_996_);
lean_inc(v_bitvecState_995_);
lean_inc(v_funState_994_);
lean_dec(v_theoryState_984_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1010_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 2, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_funState_994_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_bitvecState_995_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_satSolver_997_);
v___x_1003_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 3, v___x_1003_);
v___x_1005_ = v___x_992_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_satExpr_985_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_hypQueue_986_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_usedHyps_987_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_solverTimeBudgetMs_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 5, v_roundBudget_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*6, v_didChange_988_);
v___x_1005_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_st_ref_put(v_a_981_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_preprocessCaches_996_);
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg___boxed(lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(v_a_1012_);
lean_dec(v_a_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_theoryState_1031_; lean_object* v_satExpr_1032_; lean_object* v_hypQueue_1033_; lean_object* v_usedHyps_1034_; uint8_t v_didChange_1035_; lean_object* v_solverTimeBudgetMs_1036_; lean_object* v_roundBudget_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1058_; 
v___x_1030_ = lean_st_ref_take(v_a_1016_);
v_theoryState_1031_ = lean_ctor_get(v___x_1030_, 3);
v_satExpr_1032_ = lean_ctor_get(v___x_1030_, 0);
v_hypQueue_1033_ = lean_ctor_get(v___x_1030_, 1);
v_usedHyps_1034_ = lean_ctor_get(v___x_1030_, 2);
v_didChange_1035_ = lean_ctor_get_uint8(v___x_1030_, sizeof(void*)*6);
v_solverTimeBudgetMs_1036_ = lean_ctor_get(v___x_1030_, 4);
v_roundBudget_1037_ = lean_ctor_get(v___x_1030_, 5);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1039_ = v___x_1030_;
v_isShared_1040_ = v_isSharedCheck_1058_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_roundBudget_1037_);
lean_inc(v_solverTimeBudgetMs_1036_);
lean_inc(v_theoryState_1031_);
lean_inc(v_usedHyps_1034_);
lean_inc(v_hypQueue_1033_);
lean_inc(v_satExpr_1032_);
lean_dec(v___x_1030_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1058_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_funState_1041_; lean_object* v_bitvecState_1042_; lean_object* v_preprocessCaches_1043_; lean_object* v_satSolver_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1057_; 
v_funState_1041_ = lean_ctor_get(v_theoryState_1031_, 0);
v_bitvecState_1042_ = lean_ctor_get(v_theoryState_1031_, 1);
v_preprocessCaches_1043_ = lean_ctor_get(v_theoryState_1031_, 2);
v_satSolver_1044_ = lean_ctor_get(v_theoryState_1031_, 3);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_theoryState_1031_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1046_ = v_theoryState_1031_;
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_satSolver_1044_);
lean_inc(v_preprocessCaches_1043_);
lean_inc(v_bitvecState_1042_);
lean_inc(v_funState_1041_);
lean_dec(v_theoryState_1031_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 2, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_funState_1041_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_bitvecState_1042_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_satSolver_1044_);
v___x_1050_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v___x_1050_);
v___x_1052_ = v___x_1039_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_satExpr_1032_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_hypQueue_1033_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_usedHyps_1034_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_solverTimeBudgetMs_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 5, v_roundBudget_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1055_, sizeof(void*)*6, v_didChange_1035_);
v___x_1052_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_st_ref_put(v_a_1016_, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v_preprocessCaches_1043_);
return v___x_1054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___boxed(lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(lean_object* v_caches_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_theoryState_1079_; lean_object* v_satExpr_1080_; lean_object* v_hypQueue_1081_; lean_object* v_usedHyps_1082_; uint8_t v_didChange_1083_; lean_object* v_solverTimeBudgetMs_1084_; lean_object* v_roundBudget_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1106_; 
v___x_1078_ = lean_st_ref_take(v_a_1076_);
v_theoryState_1079_ = lean_ctor_get(v___x_1078_, 3);
v_satExpr_1080_ = lean_ctor_get(v___x_1078_, 0);
v_hypQueue_1081_ = lean_ctor_get(v___x_1078_, 1);
v_usedHyps_1082_ = lean_ctor_get(v___x_1078_, 2);
v_didChange_1083_ = lean_ctor_get_uint8(v___x_1078_, sizeof(void*)*6);
v_solverTimeBudgetMs_1084_ = lean_ctor_get(v___x_1078_, 4);
v_roundBudget_1085_ = lean_ctor_get(v___x_1078_, 5);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1087_ = v___x_1078_;
v_isShared_1088_ = v_isSharedCheck_1106_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_roundBudget_1085_);
lean_inc(v_solverTimeBudgetMs_1084_);
lean_inc(v_theoryState_1079_);
lean_inc(v_usedHyps_1082_);
lean_inc(v_hypQueue_1081_);
lean_inc(v_satExpr_1080_);
lean_dec(v___x_1078_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1106_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_funState_1089_; lean_object* v_bitvecState_1090_; lean_object* v_satSolver_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1104_; 
v_funState_1089_ = lean_ctor_get(v_theoryState_1079_, 0);
v_bitvecState_1090_ = lean_ctor_get(v_theoryState_1079_, 1);
v_satSolver_1091_ = lean_ctor_get(v_theoryState_1079_, 3);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_theoryState_1079_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v_theoryState_1079_, 2);
lean_dec(v_unused_1105_);
v___x_1093_ = v_theoryState_1079_;
v_isShared_1094_ = v_isSharedCheck_1104_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_satSolver_1091_);
lean_inc(v_bitvecState_1090_);
lean_inc(v_funState_1089_);
lean_dec(v_theoryState_1079_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1104_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_box(0);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v_caches_1075_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_funState_1089_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_bitvecState_1090_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_caches_1075_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_satSolver_1091_);
v___x_1097_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 3, v___x_1097_);
v___x_1099_ = v___x_1087_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_satExpr_1080_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_hypQueue_1081_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_usedHyps_1082_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_solverTimeBudgetMs_1084_);
lean_ctor_set(v_reuseFailAlloc_1102_, 5, v_roundBudget_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*6, v_didChange_1083_);
v___x_1099_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_st_ref_put(v_a_1076_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1095_);
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg___boxed(lean_object* v_caches_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(v_caches_1107_, v_a_1108_);
lean_dec(v_a_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(lean_object* v_caches_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_theoryState_1128_; lean_object* v_satExpr_1129_; lean_object* v_hypQueue_1130_; lean_object* v_usedHyps_1131_; uint8_t v_didChange_1132_; lean_object* v_solverTimeBudgetMs_1133_; lean_object* v_roundBudget_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1155_; 
v___x_1127_ = lean_st_ref_take(v_a_1113_);
v_theoryState_1128_ = lean_ctor_get(v___x_1127_, 3);
v_satExpr_1129_ = lean_ctor_get(v___x_1127_, 0);
v_hypQueue_1130_ = lean_ctor_get(v___x_1127_, 1);
v_usedHyps_1131_ = lean_ctor_get(v___x_1127_, 2);
v_didChange_1132_ = lean_ctor_get_uint8(v___x_1127_, sizeof(void*)*6);
v_solverTimeBudgetMs_1133_ = lean_ctor_get(v___x_1127_, 4);
v_roundBudget_1134_ = lean_ctor_get(v___x_1127_, 5);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1136_ = v___x_1127_;
v_isShared_1137_ = v_isSharedCheck_1155_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_roundBudget_1134_);
lean_inc(v_solverTimeBudgetMs_1133_);
lean_inc(v_theoryState_1128_);
lean_inc(v_usedHyps_1131_);
lean_inc(v_hypQueue_1130_);
lean_inc(v_satExpr_1129_);
lean_dec(v___x_1127_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1155_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_funState_1138_; lean_object* v_bitvecState_1139_; lean_object* v_satSolver_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1153_; 
v_funState_1138_ = lean_ctor_get(v_theoryState_1128_, 0);
v_bitvecState_1139_ = lean_ctor_get(v_theoryState_1128_, 1);
v_satSolver_1140_ = lean_ctor_get(v_theoryState_1128_, 3);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_theoryState_1128_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_theoryState_1128_, 2);
lean_dec(v_unused_1154_);
v___x_1142_ = v_theoryState_1128_;
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_satSolver_1140_);
lean_inc(v_bitvecState_1139_);
lean_inc(v_funState_1138_);
lean_dec(v_theoryState_1128_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = lean_box(0);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 2, v_caches_1111_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_funState_1138_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_bitvecState_1139_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_caches_1111_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_satSolver_1140_);
v___x_1146_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 3, v___x_1146_);
v___x_1148_ = v___x_1136_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_satExpr_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_hypQueue_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_usedHyps_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_solverTimeBudgetMs_1133_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_roundBudget_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1151_, sizeof(void*)*6, v_didChange_1132_);
v___x_1148_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_st_ref_put(v_a_1113_, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1144_);
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___boxed(lean_object* v_caches_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(v_caches_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(lean_object* v_ctx_1173_, lean_object* v_x_1174_, lean_object* v_goal_1175_, lean_object* v_reflectionResult_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_config_1191_; lean_object* v_satExpr_1192_; lean_object* v_unusedHypotheses_1193_; lean_object* v_timeout_1194_; lean_object* v_cegarRounds_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1190_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1191_ = lean_ctor_get(v_ctx_1173_, 5);
v_satExpr_1192_ = lean_ctor_get(v_reflectionResult_1176_, 0);
v_unusedHypotheses_1193_ = lean_ctor_get(v_reflectionResult_1176_, 1);
v_timeout_1194_ = lean_ctor_get(v_config_1191_, 0);
v_cegarRounds_1195_ = lean_ctor_get(v_config_1191_, 2);
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1197_ = 1;
v___x_1198_ = lean_unsigned_to_nat(1000u);
v___x_1199_ = lean_nat_mul(v_timeout_1194_, v___x_1198_);
lean_inc(v_cegarRounds_1195_);
lean_inc_ref(v_satExpr_1192_);
v___x_1200_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1200_, 0, v_satExpr_1192_);
lean_ctor_set(v___x_1200_, 1, v___x_1196_);
lean_ctor_set(v___x_1200_, 2, v___x_1196_);
lean_ctor_set(v___x_1200_, 3, v___x_1190_);
lean_ctor_set(v___x_1200_, 4, v___x_1199_);
lean_ctor_set(v___x_1200_, 5, v_cegarRounds_1195_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*6, v___x_1197_);
lean_inc_ref(v_unusedHypotheses_1193_);
v___x_1201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1201_, 0, v_goal_1175_);
lean_ctor_set(v___x_1201_, 1, v_unusedHypotheses_1193_);
lean_ctor_set(v___x_1201_, 2, v_ctx_1173_);
v___x_1202_ = lean_st_mk_ref(v___x_1200_);
lean_inc(v_a_1188_);
lean_inc_ref(v_a_1187_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
lean_inc(v_a_1182_);
lean_inc_ref(v_a_1181_);
lean_inc(v_a_1180_);
lean_inc(v_a_1179_);
lean_inc_ref(v_a_1178_);
lean_inc(v_a_1177_);
lean_inc(v___x_1202_);
v___x_1203_ = lean_apply_15(v_x_1174_, v___x_1201_, v___x_1202_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, lean_box(0));
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_st_ref_get(v___x_1202_);
lean_dec(v___x_1202_);
lean_dec(v___x_1208_);
if (v_isShared_1207_ == 0)
{
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1204_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_dec(v___x_1202_);
return v___x_1203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg___boxed(lean_object** _args){
lean_object* v_ctx_1213_ = _args[0];
lean_object* v_x_1214_ = _args[1];
lean_object* v_goal_1215_ = _args[2];
lean_object* v_reflectionResult_1216_ = _args[3];
lean_object* v_a_1217_ = _args[4];
lean_object* v_a_1218_ = _args[5];
lean_object* v_a_1219_ = _args[6];
lean_object* v_a_1220_ = _args[7];
lean_object* v_a_1221_ = _args[8];
lean_object* v_a_1222_ = _args[9];
lean_object* v_a_1223_ = _args[10];
lean_object* v_a_1224_ = _args[11];
lean_object* v_a_1225_ = _args[12];
lean_object* v_a_1226_ = _args[13];
lean_object* v_a_1227_ = _args[14];
lean_object* v_a_1228_ = _args[15];
lean_object* v_a_1229_ = _args[16];
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(v_ctx_1213_, v_x_1214_, v_goal_1215_, v_reflectionResult_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_reflectionResult_1216_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_object* v_00_u03b1_1231_, lean_object* v_ctx_1232_, lean_object* v_x_1233_, lean_object* v_goal_1234_, lean_object* v_reflectionResult_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v_config_1250_; lean_object* v_satExpr_1251_; lean_object* v_unusedHypotheses_1252_; lean_object* v_timeout_1253_; lean_object* v_cegarRounds_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1249_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1250_ = lean_ctor_get(v_ctx_1232_, 5);
v_satExpr_1251_ = lean_ctor_get(v_reflectionResult_1235_, 0);
v_unusedHypotheses_1252_ = lean_ctor_get(v_reflectionResult_1235_, 1);
v_timeout_1253_ = lean_ctor_get(v_config_1250_, 0);
v_cegarRounds_1254_ = lean_ctor_get(v_config_1250_, 2);
v___x_1255_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1256_ = 1;
v___x_1257_ = lean_unsigned_to_nat(1000u);
v___x_1258_ = lean_nat_mul(v_timeout_1253_, v___x_1257_);
lean_inc(v_cegarRounds_1254_);
lean_inc_ref(v_satExpr_1251_);
v___x_1259_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1259_, 0, v_satExpr_1251_);
lean_ctor_set(v___x_1259_, 1, v___x_1255_);
lean_ctor_set(v___x_1259_, 2, v___x_1255_);
lean_ctor_set(v___x_1259_, 3, v___x_1249_);
lean_ctor_set(v___x_1259_, 4, v___x_1258_);
lean_ctor_set(v___x_1259_, 5, v_cegarRounds_1254_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*6, v___x_1256_);
lean_inc_ref(v_unusedHypotheses_1252_);
v___x_1260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1260_, 0, v_goal_1234_);
lean_ctor_set(v___x_1260_, 1, v_unusedHypotheses_1252_);
lean_ctor_set(v___x_1260_, 2, v_ctx_1232_);
v___x_1261_ = lean_st_mk_ref(v___x_1259_);
lean_inc(v_a_1247_);
lean_inc_ref(v_a_1246_);
lean_inc(v_a_1245_);
lean_inc_ref(v_a_1244_);
lean_inc(v_a_1243_);
lean_inc_ref(v_a_1242_);
lean_inc(v_a_1241_);
lean_inc_ref(v_a_1240_);
lean_inc(v_a_1239_);
lean_inc(v_a_1238_);
lean_inc_ref(v_a_1237_);
lean_inc(v_a_1236_);
lean_inc(v___x_1261_);
v___x_1262_ = lean_apply_15(v_x_1233_, v___x_1260_, v___x_1261_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, lean_box(0));
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_st_ref_get(v___x_1261_);
lean_dec(v___x_1261_);
lean_dec(v___x_1267_);
if (v_isShared_1266_ == 0)
{
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1263_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_dec(v___x_1261_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___boxed(lean_object** _args){
lean_object* v_00_u03b1_1272_ = _args[0];
lean_object* v_ctx_1273_ = _args[1];
lean_object* v_x_1274_ = _args[2];
lean_object* v_goal_1275_ = _args[3];
lean_object* v_reflectionResult_1276_ = _args[4];
lean_object* v_a_1277_ = _args[5];
lean_object* v_a_1278_ = _args[6];
lean_object* v_a_1279_ = _args[7];
lean_object* v_a_1280_ = _args[8];
lean_object* v_a_1281_ = _args[9];
lean_object* v_a_1282_ = _args[10];
lean_object* v_a_1283_ = _args[11];
lean_object* v_a_1284_ = _args[12];
lean_object* v_a_1285_ = _args[13];
lean_object* v_a_1286_ = _args[14];
lean_object* v_a_1287_ = _args[15];
lean_object* v_a_1288_ = _args[16];
lean_object* v_a_1289_ = _args[17];
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run(v_00_u03b1_1272_, v_ctx_1273_, v_x_1274_, v_goal_1275_, v_reflectionResult_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_reflectionResult_1276_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v_theoryState_1294_; lean_object* v_satSolver_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_st_ref_get(v_a_1291_);
v_theoryState_1294_ = lean_ctor_get(v___x_1293_, 3);
lean_inc_ref(v_theoryState_1294_);
lean_dec(v___x_1293_);
v_satSolver_1295_ = lean_ctor_get(v_theoryState_1294_, 3);
lean_inc_ref(v_satSolver_1295_);
lean_dec_ref(v_theoryState_1294_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_satSolver_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg___boxed(lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1297_);
lean_dec(v_a_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1301_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___boxed(lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1331_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_instMonadEIO___redArg();
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(lean_object* v_msg_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_toApplicative_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1420_; 
v___x_1350_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0);
v___x_1351_ = l_StateRefT_x27_instMonad___redArg(v___x_1350_);
v_toApplicative_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1351_, 1);
lean_dec(v_unused_1421_);
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1420_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_toApplicative_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1420_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_toFunctor_1356_; lean_object* v_toSeq_1357_; lean_object* v_toSeqLeft_1358_; lean_object* v_toSeqRight_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1418_; 
v_toFunctor_1356_ = lean_ctor_get(v_toApplicative_1352_, 0);
v_toSeq_1357_ = lean_ctor_get(v_toApplicative_1352_, 2);
v_toSeqLeft_1358_ = lean_ctor_get(v_toApplicative_1352_, 3);
v_toSeqRight_1359_ = lean_ctor_get(v_toApplicative_1352_, 4);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_toApplicative_1352_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v_toApplicative_1352_, 1);
lean_dec(v_unused_1419_);
v___x_1361_ = v_toApplicative_1352_;
v_isShared_1362_ = v_isSharedCheck_1418_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_toSeqRight_1359_);
lean_inc(v_toSeqLeft_1358_);
lean_inc(v_toSeq_1357_);
lean_inc(v_toFunctor_1356_);
lean_dec(v_toApplicative_1352_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1418_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___f_1369_; lean_object* v___f_1370_; lean_object* v___x_1372_; 
v___f_1363_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1));
v___f_1364_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1356_);
v___f_1365_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1365_, 0, v_toFunctor_1356_);
v___f_1366_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1366_, 0, v_toFunctor_1356_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___f_1365_);
lean_ctor_set(v___x_1367_, 1, v___f_1366_);
v___f_1368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1368_, 0, v_toSeqRight_1359_);
v___f_1369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1369_, 0, v_toSeqLeft_1358_);
v___f_1370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1370_, 0, v_toSeq_1357_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v___f_1368_);
lean_ctor_set(v___x_1361_, 3, v___f_1369_);
lean_ctor_set(v___x_1361_, 2, v___f_1370_);
lean_ctor_set(v___x_1361_, 1, v___f_1363_);
lean_ctor_set(v___x_1361_, 0, v___x_1367_);
v___x_1372_ = v___x_1361_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___f_1363_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v___f_1370_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___f_1369_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___f_1368_);
v___x_1372_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___f_1364_);
lean_ctor_set(v___x_1354_, 0, v___x_1372_);
v___x_1374_ = v___x_1354_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___f_1364_);
v___x_1374_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v_toApplicative_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1414_; 
v___x_1375_ = l_StateRefT_x27_instMonad___redArg(v___x_1374_);
v_toApplicative_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1375_, 1);
lean_dec(v_unused_1415_);
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1414_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_toApplicative_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1414_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_toFunctor_1380_; lean_object* v_toSeq_1381_; lean_object* v_toSeqLeft_1382_; lean_object* v_toSeqRight_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1412_; 
v_toFunctor_1380_ = lean_ctor_get(v_toApplicative_1376_, 0);
v_toSeq_1381_ = lean_ctor_get(v_toApplicative_1376_, 2);
v_toSeqLeft_1382_ = lean_ctor_get(v_toApplicative_1376_, 3);
v_toSeqRight_1383_ = lean_ctor_get(v_toApplicative_1376_, 4);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_toApplicative_1376_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_toApplicative_1376_, 1);
lean_dec(v_unused_1413_);
v___x_1385_ = v_toApplicative_1376_;
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_toSeqRight_1383_);
lean_inc(v_toSeqLeft_1382_);
lean_inc(v_toSeq_1381_);
lean_inc(v_toFunctor_1380_);
lean_dec(v_toApplicative_1376_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___x_1396_; 
v___f_1387_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3));
v___f_1388_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4));
lean_inc_ref(v_toFunctor_1380_);
v___f_1389_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1389_, 0, v_toFunctor_1380_);
v___f_1390_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1390_, 0, v_toFunctor_1380_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___f_1389_);
lean_ctor_set(v___x_1391_, 1, v___f_1390_);
v___f_1392_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1392_, 0, v_toSeqRight_1383_);
v___f_1393_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1393_, 0, v_toSeqLeft_1382_);
v___f_1394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1394_, 0, v_toSeq_1381_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 4, v___f_1392_);
lean_ctor_set(v___x_1385_, 3, v___f_1393_);
lean_ctor_set(v___x_1385_, 2, v___f_1394_);
lean_ctor_set(v___x_1385_, 1, v___f_1387_);
lean_ctor_set(v___x_1385_, 0, v___x_1391_);
v___x_1396_ = v___x_1385_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___f_1387_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v___f_1394_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v___f_1393_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v___f_1392_);
v___x_1396_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___f_1388_);
lean_ctor_set(v___x_1378_, 0, v___x_1396_);
v___x_1398_ = v___x_1378_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___f_1388_);
v___x_1398_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_4587__overap_1408_; lean_object* v___x_1409_; 
v___x_1399_ = l_StateRefT_x27_instMonad___redArg(v___x_1398_);
v___x_1400_ = l_ReaderT_instMonad___redArg(v___x_1399_);
v___x_1401_ = l_StateRefT_x27_instMonad___redArg(v___x_1400_);
v___x_1402_ = l_ReaderT_instMonad___redArg(v___x_1401_);
v___x_1403_ = l_ReaderT_instMonad___redArg(v___x_1402_);
v___x_1404_ = l_StateRefT_x27_instMonad___redArg(v___x_1403_);
v___x_1405_ = lean_box(0);
v___x_1406_ = l_instInhabitedOfMonad___redArg(v___x_1404_, v___x_1405_);
v___f_1407_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1407_, 0, v___x_1406_);
v___x_4587__overap_1408_ = lean_panic_fn_borrowed(v___f_1407_, v_msg_1337_);
lean_dec_ref(v___f_1407_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1409_ = lean_apply_12(v___x_4587__overap_1408_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, lean_box(0));
return v___x_1409_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___boxed(lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
return v_x_1436_;
}
else
{
lean_object* v_key_1438_; lean_object* v_value_1439_; lean_object* v_tail_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1463_; 
v_key_1438_ = lean_ctor_get(v_x_1437_, 0);
v_value_1439_ = lean_ctor_get(v_x_1437_, 1);
v_tail_1440_ = lean_ctor_get(v_x_1437_, 2);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1437_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1442_ = v_x_1437_;
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_tail_1440_);
lean_inc(v_value_1439_);
lean_inc(v_key_1438_);
lean_dec(v_x_1437_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; uint64_t v___x_1445_; uint64_t v___x_1446_; uint64_t v___x_1447_; uint64_t v_fold_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1444_ = lean_array_get_size(v_x_1436_);
v___x_1445_ = l_Lean_Expr_hash(v_key_1438_);
v___x_1446_ = 32ULL;
v___x_1447_ = lean_uint64_shift_right(v___x_1445_, v___x_1446_);
v_fold_1448_ = lean_uint64_xor(v___x_1445_, v___x_1447_);
v___x_1449_ = 16ULL;
v___x_1450_ = lean_uint64_shift_right(v_fold_1448_, v___x_1449_);
v___x_1451_ = lean_uint64_xor(v_fold_1448_, v___x_1450_);
v___x_1452_ = lean_uint64_to_usize(v___x_1451_);
v___x_1453_ = lean_usize_of_nat(v___x_1444_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_sub(v___x_1453_, v___x_1454_);
v___x_1456_ = lean_usize_land(v___x_1452_, v___x_1455_);
v___x_1457_ = lean_array_uget_borrowed(v_x_1436_, v___x_1456_);
lean_inc(v___x_1457_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 2, v___x_1457_);
v___x_1459_ = v___x_1442_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_key_1438_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_value_1439_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_array_uset(v_x_1436_, v___x_1456_, v___x_1459_);
v_x_1436_ = v___x_1460_;
v_x_1437_ = v_tail_1440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(lean_object* v_i_1464_, lean_object* v_source_1465_, lean_object* v_target_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_array_get_size(v_source_1465_);
v___x_1468_ = lean_nat_dec_lt(v_i_1464_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v_source_1465_);
lean_dec(v_i_1464_);
return v_target_1466_;
}
else
{
lean_object* v_es_1469_; lean_object* v___x_1470_; lean_object* v_source_1471_; lean_object* v_target_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_es_1469_ = lean_array_fget(v_source_1465_, v_i_1464_);
v___x_1470_ = lean_box(0);
v_source_1471_ = lean_array_fset(v_source_1465_, v_i_1464_, v___x_1470_);
v_target_1472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_target_1466_, v_es_1469_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_i_1464_, v___x_1473_);
lean_dec(v_i_1464_);
v_i_1464_ = v___x_1474_;
v_source_1465_ = v_source_1471_;
v_target_1466_ = v_target_1472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(lean_object* v_data_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_nbuckets_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1477_ = lean_array_get_size(v_data_1476_);
v___x_1478_ = lean_unsigned_to_nat(2u);
v_nbuckets_1479_ = lean_nat_mul(v___x_1477_, v___x_1478_);
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_mk_array(v_nbuckets_1479_, v___x_1481_);
v___x_1483_ = lean_array_propagate_mark(v_data_1476_, v___x_1482_);
v___x_1484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v___x_1480_, v_data_1476_, v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(lean_object* v_a_1485_, lean_object* v_x_1486_){
_start:
{
if (lean_obj_tag(v_x_1486_) == 0)
{
uint8_t v___x_1487_; 
v___x_1487_ = 0;
return v___x_1487_;
}
else
{
lean_object* v_key_1488_; lean_object* v_tail_1489_; uint8_t v___x_1490_; 
v_key_1488_ = lean_ctor_get(v_x_1486_, 0);
v_tail_1489_ = lean_ctor_get(v_x_1486_, 2);
v___x_1490_ = lean_expr_eqv(v_key_1488_, v_a_1485_);
if (v___x_1490_ == 0)
{
v_x_1486_ = v_tail_1489_;
goto _start;
}
else
{
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg___boxed(lean_object* v_a_1492_, lean_object* v_x_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1492_, v_x_1493_);
lean_dec(v_x_1493_);
lean_dec_ref(v_a_1492_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(lean_object* v_a_1496_, lean_object* v_b_1497_, lean_object* v_x_1498_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_dec(v_b_1497_);
lean_dec_ref(v_a_1496_);
return v_x_1498_;
}
else
{
lean_object* v_key_1499_; lean_object* v_value_1500_; lean_object* v_tail_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1513_; 
v_key_1499_ = lean_ctor_get(v_x_1498_, 0);
v_value_1500_ = lean_ctor_get(v_x_1498_, 1);
v_tail_1501_ = lean_ctor_get(v_x_1498_, 2);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1503_ = v_x_1498_;
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_tail_1501_);
lean_inc(v_value_1500_);
lean_inc(v_key_1499_);
lean_dec(v_x_1498_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_expr_eqv(v_key_1499_, v_a_1496_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1496_, v_b_1497_, v_tail_1501_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 2, v___x_1506_);
v___x_1508_ = v___x_1503_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_key_1499_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_value_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_value_1500_);
lean_dec(v_key_1499_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v_b_1497_);
lean_ctor_set(v___x_1503_, 0, v_a_1496_);
v___x_1511_ = v___x_1503_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1496_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_b_1497_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_tail_1501_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(lean_object* v_m_1514_, lean_object* v_a_1515_, lean_object* v_b_1516_){
_start:
{
lean_object* v_size_1517_; lean_object* v_buckets_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1561_; 
v_size_1517_ = lean_ctor_get(v_m_1514_, 0);
v_buckets_1518_ = lean_ctor_get(v_m_1514_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_m_1514_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1520_ = v_m_1514_;
v_isShared_1521_ = v_isSharedCheck_1561_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_buckets_1518_);
lean_inc(v_size_1517_);
lean_dec(v_m_1514_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1561_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; uint64_t v_fold_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; uint64_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; size_t v___x_1534_; lean_object* v_bkt_1535_; uint8_t v___x_1536_; 
v___x_1522_ = lean_array_get_size(v_buckets_1518_);
v___x_1523_ = l_Lean_Expr_hash(v_a_1515_);
v___x_1524_ = 32ULL;
v___x_1525_ = lean_uint64_shift_right(v___x_1523_, v___x_1524_);
v_fold_1526_ = lean_uint64_xor(v___x_1523_, v___x_1525_);
v___x_1527_ = 16ULL;
v___x_1528_ = lean_uint64_shift_right(v_fold_1526_, v___x_1527_);
v___x_1529_ = lean_uint64_xor(v_fold_1526_, v___x_1528_);
v___x_1530_ = lean_uint64_to_usize(v___x_1529_);
v___x_1531_ = lean_usize_of_nat(v___x_1522_);
v___x_1532_ = ((size_t)1ULL);
v___x_1533_ = lean_usize_sub(v___x_1531_, v___x_1532_);
v___x_1534_ = lean_usize_land(v___x_1530_, v___x_1533_);
v_bkt_1535_ = lean_array_uget_borrowed(v_buckets_1518_, v___x_1534_);
v___x_1536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1515_, v_bkt_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v_size_x27_1538_; lean_object* v___x_1539_; lean_object* v_buckets_x27_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
v_size_x27_1538_ = lean_nat_add(v_size_1517_, v___x_1537_);
lean_dec(v_size_1517_);
lean_inc(v_bkt_1535_);
v___x_1539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1539_, 0, v_a_1515_);
lean_ctor_set(v___x_1539_, 1, v_b_1516_);
lean_ctor_set(v___x_1539_, 2, v_bkt_1535_);
v_buckets_x27_1540_ = lean_array_uset(v_buckets_1518_, v___x_1534_, v___x_1539_);
v___x_1541_ = lean_unsigned_to_nat(4u);
v___x_1542_ = lean_nat_mul(v_size_x27_1538_, v___x_1541_);
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = lean_nat_div(v___x_1542_, v___x_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_array_get_size(v_buckets_x27_1540_);
v___x_1546_ = lean_nat_dec_le(v___x_1544_, v___x_1545_);
lean_dec(v___x_1544_);
if (v___x_1546_ == 0)
{
lean_object* v_val_1547_; lean_object* v___x_1549_; 
v_val_1547_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_buckets_x27_1540_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v_val_1547_);
lean_ctor_set(v___x_1520_, 0, v_size_x27_1538_);
v___x_1549_ = v___x_1520_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_size_x27_1538_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_val_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
else
{
lean_object* v___x_1552_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v_buckets_x27_1540_);
lean_ctor_set(v___x_1520_, 0, v_size_x27_1538_);
v___x_1552_ = v___x_1520_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_size_x27_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_buckets_x27_1540_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v___x_1554_; lean_object* v_buckets_x27_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_inc(v_bkt_1535_);
v___x_1554_ = lean_box(0);
v_buckets_x27_1555_ = lean_array_uset(v_buckets_1518_, v___x_1534_, v___x_1554_);
v___x_1556_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1515_, v_b_1516_, v_bkt_1535_);
v___x_1557_ = lean_array_uset(v_buckets_x27_1555_, v___x_1534_, v___x_1556_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v___x_1557_);
v___x_1559_ = v___x_1520_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_size_1517_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(lean_object* v_a_1562_, lean_object* v_b_1563_, lean_object* v_x_1564_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_dec(v_b_1563_);
lean_dec(v_a_1562_);
return v_x_1564_;
}
else
{
lean_object* v_key_1565_; lean_object* v_value_1566_; lean_object* v_tail_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1579_; 
v_key_1565_ = lean_ctor_get(v_x_1564_, 0);
v_value_1566_ = lean_ctor_get(v_x_1564_, 1);
v_tail_1567_ = lean_ctor_get(v_x_1564_, 2);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1564_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1569_ = v_x_1564_;
v_isShared_1570_ = v_isSharedCheck_1579_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_tail_1567_);
lean_inc(v_value_1566_);
lean_inc(v_key_1565_);
lean_dec(v_x_1564_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1579_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_eq(v_key_1565_, v_a_1562_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1562_, v_b_1563_, v_tail_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 2, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_key_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_value_1566_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v___x_1577_; 
lean_dec(v_value_1566_);
lean_dec(v_key_1565_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_b_1563_);
lean_ctor_set(v___x_1569_, 0, v_a_1562_);
v___x_1577_ = v___x_1569_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1562_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_b_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_tail_1567_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(lean_object* v_a_1580_, lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
uint8_t v___x_1582_; 
v___x_1582_ = 0;
return v___x_1582_;
}
else
{
lean_object* v_key_1583_; lean_object* v_tail_1584_; uint8_t v___x_1585_; 
v_key_1583_ = lean_ctor_get(v_x_1581_, 0);
v_tail_1584_ = lean_ctor_get(v_x_1581_, 2);
v___x_1585_ = lean_nat_dec_eq(v_key_1583_, v_a_1580_);
if (v___x_1585_ == 0)
{
v_x_1581_ = v_tail_1584_;
goto _start;
}
else
{
return v___x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg___boxed(lean_object* v_a_1587_, lean_object* v_x_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec(v_a_1587_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
return v_x_1591_;
}
else
{
lean_object* v_key_1593_; lean_object* v_value_1594_; lean_object* v_tail_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1618_; 
v_key_1593_ = lean_ctor_get(v_x_1592_, 0);
v_value_1594_ = lean_ctor_get(v_x_1592_, 1);
v_tail_1595_ = lean_ctor_get(v_x_1592_, 2);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1597_ = v_x_1592_;
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_tail_1595_);
lean_inc(v_value_1594_);
lean_inc(v_key_1593_);
lean_dec(v_x_1592_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; uint64_t v___x_1600_; uint64_t v___x_1601_; uint64_t v___x_1602_; uint64_t v_fold_1603_; uint64_t v___x_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1599_ = lean_array_get_size(v_x_1591_);
v___x_1600_ = lean_uint64_of_nat(v_key_1593_);
v___x_1601_ = 32ULL;
v___x_1602_ = lean_uint64_shift_right(v___x_1600_, v___x_1601_);
v_fold_1603_ = lean_uint64_xor(v___x_1600_, v___x_1602_);
v___x_1604_ = 16ULL;
v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
v___x_1608_ = lean_usize_of_nat(v___x_1599_);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
v___x_1612_ = lean_array_uget_borrowed(v_x_1591_, v___x_1611_);
lean_inc(v___x_1612_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 2, v___x_1612_);
v___x_1614_ = v___x_1597_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_key_1593_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_value_1594_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_array_uset(v_x_1591_, v___x_1611_, v___x_1614_);
v_x_1591_ = v___x_1615_;
v_x_1592_ = v_tail_1595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(lean_object* v_i_1619_, lean_object* v_source_1620_, lean_object* v_target_1621_){
_start:
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_array_get_size(v_source_1620_);
v___x_1623_ = lean_nat_dec_lt(v_i_1619_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v_source_1620_);
lean_dec(v_i_1619_);
return v_target_1621_;
}
else
{
lean_object* v_es_1624_; lean_object* v___x_1625_; lean_object* v_source_1626_; lean_object* v_target_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_es_1624_ = lean_array_fget(v_source_1620_, v_i_1619_);
v___x_1625_ = lean_box(0);
v_source_1626_ = lean_array_fset(v_source_1620_, v_i_1619_, v___x_1625_);
v_target_1627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1621_, v_es_1624_);
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_add(v_i_1619_, v___x_1628_);
lean_dec(v_i_1619_);
v_i_1619_ = v___x_1629_;
v_source_1620_ = v_source_1626_;
v_target_1621_ = v_target_1627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(lean_object* v_data_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_nbuckets_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1632_ = lean_array_get_size(v_data_1631_);
v___x_1633_ = lean_unsigned_to_nat(2u);
v_nbuckets_1634_ = lean_nat_mul(v___x_1632_, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_mk_array(v_nbuckets_1634_, v___x_1636_);
v___x_1638_ = lean_array_propagate_mark(v_data_1631_, v___x_1637_);
v___x_1639_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v___x_1635_, v_data_1631_, v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(lean_object* v_m_1640_, lean_object* v_a_1641_, lean_object* v_b_1642_){
_start:
{
lean_object* v_size_1643_; lean_object* v_buckets_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1687_; 
v_size_1643_ = lean_ctor_get(v_m_1640_, 0);
v_buckets_1644_ = lean_ctor_get(v_m_1640_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_m_1640_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1646_ = v_m_1640_;
v_isShared_1647_ = v_isSharedCheck_1687_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_buckets_1644_);
lean_inc(v_size_1643_);
lean_dec(v_m_1640_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1687_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; uint64_t v___x_1649_; uint64_t v___x_1650_; uint64_t v___x_1651_; uint64_t v_fold_1652_; uint64_t v___x_1653_; uint64_t v___x_1654_; uint64_t v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; lean_object* v_bkt_1661_; uint8_t v___x_1662_; 
v___x_1648_ = lean_array_get_size(v_buckets_1644_);
v___x_1649_ = lean_uint64_of_nat(v_a_1641_);
v___x_1650_ = 32ULL;
v___x_1651_ = lean_uint64_shift_right(v___x_1649_, v___x_1650_);
v_fold_1652_ = lean_uint64_xor(v___x_1649_, v___x_1651_);
v___x_1653_ = 16ULL;
v___x_1654_ = lean_uint64_shift_right(v_fold_1652_, v___x_1653_);
v___x_1655_ = lean_uint64_xor(v_fold_1652_, v___x_1654_);
v___x_1656_ = lean_uint64_to_usize(v___x_1655_);
v___x_1657_ = lean_usize_of_nat(v___x_1648_);
v___x_1658_ = ((size_t)1ULL);
v___x_1659_ = lean_usize_sub(v___x_1657_, v___x_1658_);
v___x_1660_ = lean_usize_land(v___x_1656_, v___x_1659_);
v_bkt_1661_ = lean_array_uget_borrowed(v_buckets_1644_, v___x_1660_);
v___x_1662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1641_, v_bkt_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v_size_x27_1664_; lean_object* v___x_1665_; lean_object* v_buckets_x27_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1663_ = lean_unsigned_to_nat(1u);
v_size_x27_1664_ = lean_nat_add(v_size_1643_, v___x_1663_);
lean_dec(v_size_1643_);
lean_inc(v_bkt_1661_);
v___x_1665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1665_, 0, v_a_1641_);
lean_ctor_set(v___x_1665_, 1, v_b_1642_);
lean_ctor_set(v___x_1665_, 2, v_bkt_1661_);
v_buckets_x27_1666_ = lean_array_uset(v_buckets_1644_, v___x_1660_, v___x_1665_);
v___x_1667_ = lean_unsigned_to_nat(4u);
v___x_1668_ = lean_nat_mul(v_size_x27_1664_, v___x_1667_);
v___x_1669_ = lean_unsigned_to_nat(3u);
v___x_1670_ = lean_nat_div(v___x_1668_, v___x_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_array_get_size(v_buckets_x27_1666_);
v___x_1672_ = lean_nat_dec_le(v___x_1670_, v___x_1671_);
lean_dec(v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v_val_1673_; lean_object* v___x_1675_; 
v_val_1673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_buckets_x27_1666_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v_val_1673_);
lean_ctor_set(v___x_1646_, 0, v_size_x27_1664_);
v___x_1675_ = v___x_1646_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_size_x27_1664_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_val_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1678_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v_buckets_x27_1666_);
lean_ctor_set(v___x_1646_, 0, v_size_x27_1664_);
v___x_1678_ = v___x_1646_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_size_x27_1664_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_buckets_x27_1666_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v___x_1680_; lean_object* v_buckets_x27_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
lean_inc(v_bkt_1661_);
v___x_1680_ = lean_box(0);
v_buckets_x27_1681_ = lean_array_uset(v_buckets_1644_, v___x_1660_, v___x_1680_);
v___x_1682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1641_, v_b_1642_, v_bkt_1661_);
v___x_1683_ = lean_array_uset(v_buckets_x27_1681_, v___x_1660_, v___x_1682_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v___x_1683_);
v___x_1685_ = v___x_1646_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_size_1643_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2));
v___x_1692_ = lean_unsigned_to_nat(48u);
v___x_1693_ = lean_unsigned_to_nat(274u);
v___x_1694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1));
v___x_1695_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0));
v___x_1696_ = l_mkPanicMessageWithDecl(v___x_1695_, v___x_1694_, v___x_1693_, v___x_1692_, v___x_1691_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(lean_object* v_as_1697_, size_t v_sz_1698_, size_t v_i_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_a_1714_; uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1699_, v_sz_1698_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1700_);
return v___x_1719_;
}
else
{
lean_object* v_a_1720_; lean_object* v_snd_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v_fst_1724_; lean_object* v_snd_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1758_; 
v_a_1720_ = lean_array_uget_borrowed(v_as_1697_, v_i_1699_);
v_snd_1721_ = lean_ctor_get(v_a_1720_, 1);
v_fst_1722_ = lean_ctor_get(v_a_1720_, 0);
v_snd_1723_ = lean_ctor_get(v_snd_1721_, 1);
v_fst_1724_ = lean_ctor_get(v_b_1700_, 0);
v_snd_1725_ = lean_ctor_get(v_b_1700_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_b_1700_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1727_ = v_b_1700_;
v_isShared_1728_ = v_isSharedCheck_1758_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1725_);
lean_inc(v_fst_1724_);
lean_dec(v_b_1700_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1758_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_fst_1722_, v___y_1702_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
if (lean_obj_tag(v_a_1730_) == 1)
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v_val_1731_ = lean_ctor_get(v_a_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v_a_1730_, 1);
lean_inc_n(v_snd_1723_, 2);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_snd_1725_, v_val_1731_, v_snd_1723_);
lean_inc(v_fst_1722_);
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_fst_1724_, v_fst_1722_, v_snd_1723_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1732_);
lean_ctor_set(v___x_1727_, 0, v___x_1733_);
v___x_1735_ = v___x_1727_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1732_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
v_a_1714_ = v___x_1735_;
goto v___jp_1713_;
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_a_1730_);
v___x_1737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3);
v___x_1738_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v___x_1737_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref_known(v___x_1738_, 1);
if (v_isShared_1728_ == 0)
{
v___x_1740_ = v___x_1727_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_fst_1724_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_snd_1725_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
v_a_1714_ = v___x_1740_;
goto v___jp_1713_;
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_del_object(v___x_1727_);
lean_dec(v_snd_1725_);
lean_dec(v_fst_1724_);
v_a_1742_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1738_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1738_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1727_);
lean_dec(v_snd_1725_);
lean_dec(v_fst_1724_);
v_a_1750_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1729_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1729_);
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
v___jp_1713_:
{
size_t v___x_1715_; size_t v___x_1716_; 
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1699_, v___x_1715_);
v_i_1699_ = v___x_1716_;
v_b_1700_ = v_a_1714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___boxed(lean_object* v_as_1759_, lean_object* v_sz_1760_, lean_object* v_i_1761_, lean_object* v_b_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
size_t v_sz_boxed_1775_; size_t v_i_boxed_1776_; lean_object* v_res_1777_; 
v_sz_boxed_1775_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1776_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_as_1759_, v_sz_boxed_1775_, v_i_boxed_1776_, v_b_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec_ref(v_as_1759_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object* v_arr_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_exprCex_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_atomCex_1801_; lean_object* v___x_1802_; size_t v_sz_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_box(0);
v_exprCex_1793_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default___closed__1);
v___x_1794_ = lean_array_get_size(v_arr_1778_);
v___x_1795_ = lean_unsigned_to_nat(4u);
v___x_1796_ = lean_nat_mul(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_unsigned_to_nat(3u);
v___x_1798_ = lean_nat_div(v___x_1796_, v___x_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = l_Nat_nextPowerOfTwo(v___x_1798_);
lean_dec(v___x_1798_);
v___x_1800_ = lean_mk_array(v___x_1799_, v___x_1792_);
v_atomCex_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_atomCex_1801_, 0, v___x_1791_);
lean_ctor_set(v_atomCex_1801_, 1, v___x_1800_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_exprCex_1793_);
lean_ctor_set(v___x_1802_, 1, v_atomCex_1801_);
v_sz_1803_ = lean_array_size(v_arr_1778_);
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_arr_1778_, v_sz_1803_, v___x_1804_, v___x_1802_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1822_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1822_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1822_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_fst_1810_; lean_object* v_snd_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
v_fst_1810_ = lean_ctor_get(v_a_1806_, 0);
v_snd_1811_ = lean_ctor_get(v_a_1806_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_a_1806_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1813_ = v_a_1806_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_snd_1811_);
lean_inc(v_fst_1810_);
lean_dec(v_a_1806_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_fst_1810_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1811_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1816_);
v___x_1818_ = v___x_1808_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1805_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1805_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object* v_arr_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_arr_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec_ref(v_arr_1831_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0(lean_object* v_00_u03b2_1845_, lean_object* v_m_1846_, lean_object* v_a_1847_, lean_object* v_b_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_m_1846_, v_a_1847_, v_b_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1(lean_object* v_00_u03b2_1850_, lean_object* v_m_1851_, lean_object* v_a_1852_, lean_object* v_b_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_m_1851_, v_a_1852_, v_b_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_object* v_00_u03b2_1855_, lean_object* v_a_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_a_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(v_00_u03b2_1859_, v_a_1860_, v_x_1861_);
lean_dec(v_x_1861_);
lean_dec(v_a_1860_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1(lean_object* v_00_u03b2_1864_, lean_object* v_data_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_data_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2(lean_object* v_00_u03b2_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1868_, v_b_1869_, v_x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_object* v_00_u03b2_1872_, lean_object* v_a_1873_, lean_object* v_x_1874_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1873_, v_x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1876_, lean_object* v_a_1877_, lean_object* v_x_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(v_00_u03b2_1876_, v_a_1877_, v_x_1878_);
lean_dec(v_x_1878_);
lean_dec_ref(v_a_1877_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5(lean_object* v_00_u03b2_1881_, lean_object* v_data_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_data_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6(lean_object* v_00_u03b2_1884_, lean_object* v_a_1885_, lean_object* v_b_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1885_, v_b_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1889_, lean_object* v_i_1890_, lean_object* v_source_1891_, lean_object* v_target_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v_i_1890_, v_source_1891_, v_target_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8(lean_object* v_00_u03b2_1894_, lean_object* v_i_1895_, lean_object* v_source_1896_, lean_object* v_target_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v_i_1895_, v_source_1896_, v_target_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1900_, v_x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_x_1904_, v_x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object* v_cert_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_cert_1911_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object* v_cert_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v_usedHyps_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_st_ref_get(v_a_1916_);
v_usedHyps_1919_ = lean_ctor_get(v___x_1918_, 2);
lean_inc_ref(v_usedHyps_1919_);
lean_dec(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_usedHyps_1919_);
lean_ctor_set(v___x_1920_, 1, v_cert_1915_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg___boxed(lean_object* v_cert_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1922_, v_a_1923_);
lean_dec(v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(lean_object* v_cert_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1926_, v_a_1928_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___boxed(lean_object* v_cert_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(v_cert_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1959_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Cadical_Basic(uint8_t builtin);
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
l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry_default);
l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_FunModel_instInhabitedEntry);
l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel_default);
l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel = _init_l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Cegar_instInhabitedFunModel);
l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0 = _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0);
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
