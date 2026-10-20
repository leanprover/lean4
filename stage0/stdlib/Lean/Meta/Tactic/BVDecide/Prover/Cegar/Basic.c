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
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_unsigned_to_nat(16u);
v___x_7_ = lean_mk_array(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__1);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__2);
v___x_12_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__0));
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0___closed__3);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(lean_object* v_aig_15_){
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1___boxed(lean_object* v_aig_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_21_);
lean_dec_ref(v_aig_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(lean_object* v_aig_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___closed__0));
v___x_27_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1_spec__1(v_aig_25_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1___boxed(lean_object* v_aig_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v_aig_29_);
lean_dec_ref(v_aig_29_);
return v_res_30_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_38_ = l_Std_Sat_AIG_toCNF_State_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__1(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__2);
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_41_ = l_Std_Sat_AIG_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_spec__0;
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_43_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__4);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__5);
v___x_47_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
lean_ctor_set(v___x_47_, 2, v___x_46_);
lean_ctor_set(v___x_47_, 3, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_49_ = l_Lean_Cadical_Solver_new();
v___x_50_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_51_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__3);
v___x_52_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
lean_ctor_set(v___x_53_, 3, v___x_49_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___boxed(lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_satExpr_60_; lean_object* v_unusedHypotheses_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_59_ = lean_st_ref_get(v_a_57_);
v_satExpr_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_satExpr_60_);
lean_dec(v___x_59_);
v_unusedHypotheses_61_ = lean_ctor_get(v_a_56_, 1);
lean_inc_ref(v_unusedHypotheses_61_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_satExpr_60_);
lean_ctor_set(v___x_62_, 1, v_unusedHypotheses_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg___boxed(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_68_, v_a_69_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___boxed(lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; uint8_t v_didChange_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_st_ref_get(v_a_100_);
v_didChange_103_ = lean_ctor_get_uint8(v___x_102_, sizeof(void*)*6);
lean_dec(v___x_102_);
v___x_104_ = lean_box(v_didChange_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg___boxed(lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(v_a_106_);
lean_dec(v_a_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; uint8_t v_didChange_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = lean_st_ref_get(v_a_110_);
v_didChange_125_ = lean_ctor_get_uint8(v___x_124_, sizeof(void*)*6);
lean_dec(v___x_124_);
v___x_126_ = lean_box(v_didChange_125_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___boxed(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(uint8_t v_v_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; lean_object* v_satExpr_148_; lean_object* v_hypQueue_149_; lean_object* v_usedHyps_150_; lean_object* v_theoryState_151_; lean_object* v_solverTimeBudgetMs_152_; lean_object* v_roundBudget_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_163_; 
v___x_147_ = lean_st_ref_take(v_a_145_);
v_satExpr_148_ = lean_ctor_get(v___x_147_, 0);
v_hypQueue_149_ = lean_ctor_get(v___x_147_, 1);
v_usedHyps_150_ = lean_ctor_get(v___x_147_, 2);
v_theoryState_151_ = lean_ctor_get(v___x_147_, 3);
v_solverTimeBudgetMs_152_ = lean_ctor_get(v___x_147_, 4);
v_roundBudget_153_ = lean_ctor_get(v___x_147_, 5);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_163_ == 0)
{
v___x_155_ = v___x_147_;
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_roundBudget_153_);
lean_inc(v_solverTimeBudgetMs_152_);
lean_inc(v_theoryState_151_);
lean_inc(v_usedHyps_150_);
lean_inc(v_hypQueue_149_);
lean_inc(v_satExpr_148_);
lean_dec(v___x_147_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
if (v_isShared_156_ == 0)
{
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_satExpr_148_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_hypQueue_149_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_usedHyps_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_theoryState_151_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_solverTimeBudgetMs_152_);
lean_ctor_set(v_reuseFailAlloc_162_, 5, v_roundBudget_153_);
v___x_159_ = v_reuseFailAlloc_162_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*6, v_v_144_);
v___x_160_ = lean_st_ref_put(v_a_145_, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_157_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg___boxed(lean_object* v_v_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_v_boxed_167_; lean_object* v_res_168_; 
v_v_boxed_167_ = lean_unbox(v_v_164_);
v_res_168_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(v_v_boxed_167_, v_a_165_);
lean_dec(v_a_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(uint8_t v_v_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_satExpr_186_; lean_object* v_hypQueue_187_; lean_object* v_usedHyps_188_; lean_object* v_theoryState_189_; lean_object* v_solverTimeBudgetMs_190_; lean_object* v_roundBudget_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v___x_185_ = lean_st_ref_take(v_a_171_);
v_satExpr_186_ = lean_ctor_get(v___x_185_, 0);
v_hypQueue_187_ = lean_ctor_get(v___x_185_, 1);
v_usedHyps_188_ = lean_ctor_get(v___x_185_, 2);
v_theoryState_189_ = lean_ctor_get(v___x_185_, 3);
v_solverTimeBudgetMs_190_ = lean_ctor_get(v___x_185_, 4);
v_roundBudget_191_ = lean_ctor_get(v___x_185_, 5);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v___x_185_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_roundBudget_191_);
lean_inc(v_solverTimeBudgetMs_190_);
lean_inc(v_theoryState_189_);
lean_inc(v_usedHyps_188_);
lean_inc(v_hypQueue_187_);
lean_inc(v_satExpr_186_);
lean_dec(v___x_185_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
if (v_isShared_194_ == 0)
{
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_satExpr_186_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_hypQueue_187_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_usedHyps_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_theoryState_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_solverTimeBudgetMs_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 5, v_roundBudget_191_);
v___x_197_ = v_reuseFailAlloc_200_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*6, v_v_169_);
v___x_198_ = lean_st_ref_put(v_a_171_, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_195_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___boxed(lean_object* v_v_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
uint8_t v_v_boxed_218_; lean_object* v_res_219_; 
v_v_boxed_218_ = lean_unbox(v_v_202_);
v_res_219_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(v_v_boxed_218_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(lean_object* v_a_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_theoryState_223_; lean_object* v___x_224_; 
v___x_222_ = lean_st_ref_get(v_a_220_);
v_theoryState_223_ = lean_ctor_get(v___x_222_, 3);
lean_inc_ref(v_theoryState_223_);
lean_dec(v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_theoryState_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg___boxed(lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(v_a_225_);
lean_dec(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; lean_object* v_theoryState_244_; lean_object* v___x_245_; 
v___x_243_ = lean_st_ref_get(v_a_229_);
v_theoryState_244_ = lean_ctor_get(v___x_243_, 3);
lean_inc_ref(v_theoryState_244_);
lean_dec(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_theoryState_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___boxed(lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(lean_object* v_f_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; lean_object* v_satExpr_266_; lean_object* v_hypQueue_267_; lean_object* v_usedHyps_268_; uint8_t v_didChange_269_; lean_object* v_theoryState_270_; lean_object* v_solverTimeBudgetMs_271_; lean_object* v_roundBudget_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_283_; 
v___x_265_ = lean_st_ref_take(v_a_263_);
v_satExpr_266_ = lean_ctor_get(v___x_265_, 0);
v_hypQueue_267_ = lean_ctor_get(v___x_265_, 1);
v_usedHyps_268_ = lean_ctor_get(v___x_265_, 2);
v_didChange_269_ = lean_ctor_get_uint8(v___x_265_, sizeof(void*)*6);
v_theoryState_270_ = lean_ctor_get(v___x_265_, 3);
v_solverTimeBudgetMs_271_ = lean_ctor_get(v___x_265_, 4);
v_roundBudget_272_ = lean_ctor_get(v___x_265_, 5);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_283_ == 0)
{
v___x_274_ = v___x_265_;
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_roundBudget_272_);
lean_inc(v_solverTimeBudgetMs_271_);
lean_inc(v_theoryState_270_);
lean_inc(v_usedHyps_268_);
lean_inc(v_hypQueue_267_);
lean_inc(v_satExpr_266_);
lean_dec(v___x_265_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_283_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v_f_262_, v_theoryState_270_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 3, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_satExpr_266_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_hypQueue_267_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_usedHyps_268_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_solverTimeBudgetMs_271_);
lean_ctor_set(v_reuseFailAlloc_282_, 5, v_roundBudget_272_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*6, v_didChange_269_);
v___x_279_ = v_reuseFailAlloc_282_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_st_ref_put(v_a_263_, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_276_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg___boxed(lean_object* v_f_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(v_f_284_, v_a_285_);
lean_dec(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(lean_object* v_f_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; lean_object* v_satExpr_305_; lean_object* v_hypQueue_306_; lean_object* v_usedHyps_307_; uint8_t v_didChange_308_; lean_object* v_theoryState_309_; lean_object* v_solverTimeBudgetMs_310_; lean_object* v_roundBudget_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_322_; 
v___x_304_ = lean_st_ref_take(v_a_290_);
v_satExpr_305_ = lean_ctor_get(v___x_304_, 0);
v_hypQueue_306_ = lean_ctor_get(v___x_304_, 1);
v_usedHyps_307_ = lean_ctor_get(v___x_304_, 2);
v_didChange_308_ = lean_ctor_get_uint8(v___x_304_, sizeof(void*)*6);
v_theoryState_309_ = lean_ctor_get(v___x_304_, 3);
v_solverTimeBudgetMs_310_ = lean_ctor_get(v___x_304_, 4);
v_roundBudget_311_ = lean_ctor_get(v___x_304_, 5);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_322_ == 0)
{
v___x_313_ = v___x_304_;
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_roundBudget_311_);
lean_inc(v_solverTimeBudgetMs_310_);
lean_inc(v_theoryState_309_);
lean_inc(v_usedHyps_307_);
lean_inc(v_hypQueue_306_);
lean_inc(v_satExpr_305_);
lean_dec(v___x_304_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_f_288_, v_theoryState_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_satExpr_305_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_hypQueue_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_usedHyps_307_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_solverTimeBudgetMs_310_);
lean_ctor_set(v_reuseFailAlloc_321_, 5, v_roundBudget_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*6, v_didChange_308_);
v___x_318_ = v_reuseFailAlloc_321_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_st_ref_put(v_a_290_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_315_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___boxed(lean_object* v_f_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(v_f_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_Sat_AIG_empty___redArg();
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_342_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1);
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_345_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; lean_object* v_satExpr_350_; lean_object* v_hypQueue_351_; lean_object* v_usedHyps_352_; uint8_t v_didChange_353_; lean_object* v_theoryState_354_; lean_object* v_solverTimeBudgetMs_355_; lean_object* v_roundBudget_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_380_; 
v___x_349_ = lean_st_ref_take(v_a_347_);
v_satExpr_350_ = lean_ctor_get(v___x_349_, 0);
v_hypQueue_351_ = lean_ctor_get(v___x_349_, 1);
v_usedHyps_352_ = lean_ctor_get(v___x_349_, 2);
v_didChange_353_ = lean_ctor_get_uint8(v___x_349_, sizeof(void*)*6);
v_theoryState_354_ = lean_ctor_get(v___x_349_, 3);
v_solverTimeBudgetMs_355_ = lean_ctor_get(v___x_349_, 4);
v_roundBudget_356_ = lean_ctor_get(v___x_349_, 5);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_380_ == 0)
{
v___x_358_ = v___x_349_;
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_roundBudget_356_);
lean_inc(v_solverTimeBudgetMs_355_);
lean_inc(v_theoryState_354_);
lean_inc(v_usedHyps_352_);
lean_inc(v_hypQueue_351_);
lean_inc(v_satExpr_350_);
lean_dec(v___x_349_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_380_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v_satSolver_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_376_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_361_ = lean_ctor_get(v_theoryState_354_, 3);
v_isSharedCheck_376_ = !lean_is_exclusive(v_theoryState_354_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_377_ = lean_ctor_get(v_theoryState_354_, 2);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_theoryState_354_, 1);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_theoryState_354_, 0);
lean_dec(v_unused_379_);
v___x_363_ = v_theoryState_354_;
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_satSolver_361_);
lean_dec(v_theoryState_354_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_366_ = lean_box(0);
v___x_367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 2, v___x_360_);
lean_ctor_set(v___x_363_, 1, v___x_367_);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_369_ = v___x_363_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_satSolver_361_);
v___x_369_ = v_reuseFailAlloc_375_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 3, v___x_369_);
v___x_371_ = v___x_358_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_satExpr_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_hypQueue_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_usedHyps_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_solverTimeBudgetMs_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_roundBudget_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*6, v_didChange_353_);
v___x_371_ = v_reuseFailAlloc_374_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_st_ref_put(v_a_347_, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_366_);
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___boxed(lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(v_a_381_);
lean_dec(v_a_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_satExpr_400_; lean_object* v_hypQueue_401_; lean_object* v_usedHyps_402_; uint8_t v_didChange_403_; lean_object* v_theoryState_404_; lean_object* v_solverTimeBudgetMs_405_; lean_object* v_roundBudget_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_430_; 
v___x_399_ = lean_st_ref_take(v_a_385_);
v_satExpr_400_ = lean_ctor_get(v___x_399_, 0);
v_hypQueue_401_ = lean_ctor_get(v___x_399_, 1);
v_usedHyps_402_ = lean_ctor_get(v___x_399_, 2);
v_didChange_403_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*6);
v_theoryState_404_ = lean_ctor_get(v___x_399_, 3);
v_solverTimeBudgetMs_405_ = lean_ctor_get(v___x_399_, 4);
v_roundBudget_406_ = lean_ctor_get(v___x_399_, 5);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_430_ == 0)
{
v___x_408_ = v___x_399_;
v_isShared_409_ = v_isSharedCheck_430_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_roundBudget_406_);
lean_inc(v_solverTimeBudgetMs_405_);
lean_inc(v_theoryState_404_);
lean_inc(v_usedHyps_402_);
lean_inc(v_hypQueue_401_);
lean_inc(v_satExpr_400_);
lean_dec(v___x_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_430_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v_satSolver_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_426_; 
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_411_ = lean_ctor_get(v_theoryState_404_, 3);
v_isSharedCheck_426_ = !lean_is_exclusive(v_theoryState_404_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_427_ = lean_ctor_get(v_theoryState_404_, 2);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_theoryState_404_, 1);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_theoryState_404_, 0);
lean_dec(v_unused_429_);
v___x_413_ = v_theoryState_404_;
v_isShared_414_ = v_isSharedCheck_426_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_satSolver_411_);
lean_dec(v_theoryState_404_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_426_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_416_ = lean_box(0);
v___x_417_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set(v___x_413_, 1, v___x_417_);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_419_ = v___x_413_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_satSolver_411_);
v___x_419_ = v_reuseFailAlloc_425_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 3, v___x_419_);
v___x_421_ = v___x_408_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_satExpr_400_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_hypQueue_401_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_usedHyps_402_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_solverTimeBudgetMs_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v_roundBudget_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_424_, sizeof(void*)*6, v_didChange_403_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_st_ref_put(v_a_385_, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_416_);
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___boxed(lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(lean_object* v_hyp_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v_satExpr_451_; lean_object* v_hypQueue_452_; lean_object* v_usedHyps_453_; uint8_t v_didChange_454_; lean_object* v_theoryState_455_; lean_object* v_solverTimeBudgetMs_456_; lean_object* v_roundBudget_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_468_; 
v___x_450_ = lean_st_ref_take(v_a_448_);
v_satExpr_451_ = lean_ctor_get(v___x_450_, 0);
v_hypQueue_452_ = lean_ctor_get(v___x_450_, 1);
v_usedHyps_453_ = lean_ctor_get(v___x_450_, 2);
v_didChange_454_ = lean_ctor_get_uint8(v___x_450_, sizeof(void*)*6);
v_theoryState_455_ = lean_ctor_get(v___x_450_, 3);
v_solverTimeBudgetMs_456_ = lean_ctor_get(v___x_450_, 4);
v_roundBudget_457_ = lean_ctor_get(v___x_450_, 5);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_468_ == 0)
{
v___x_459_ = v___x_450_;
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_roundBudget_457_);
lean_inc(v_solverTimeBudgetMs_456_);
lean_inc(v_theoryState_455_);
lean_inc(v_usedHyps_453_);
lean_inc(v_hypQueue_452_);
lean_inc(v_satExpr_451_);
lean_dec(v___x_450_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_468_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_array_push(v_hypQueue_452_, v_hyp_447_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_satExpr_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_usedHyps_453_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_theoryState_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_solverTimeBudgetMs_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 5, v_roundBudget_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_467_, sizeof(void*)*6, v_didChange_454_);
v___x_464_ = v_reuseFailAlloc_467_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_st_ref_put(v_a_448_, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_461_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg___boxed(lean_object* v_hyp_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(v_hyp_469_, v_a_470_);
lean_dec(v_a_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(lean_object* v_hyp_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; lean_object* v_satExpr_490_; lean_object* v_hypQueue_491_; lean_object* v_usedHyps_492_; uint8_t v_didChange_493_; lean_object* v_theoryState_494_; lean_object* v_solverTimeBudgetMs_495_; lean_object* v_roundBudget_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_507_; 
v___x_489_ = lean_st_ref_take(v_a_475_);
v_satExpr_490_ = lean_ctor_get(v___x_489_, 0);
v_hypQueue_491_ = lean_ctor_get(v___x_489_, 1);
v_usedHyps_492_ = lean_ctor_get(v___x_489_, 2);
v_didChange_493_ = lean_ctor_get_uint8(v___x_489_, sizeof(void*)*6);
v_theoryState_494_ = lean_ctor_get(v___x_489_, 3);
v_solverTimeBudgetMs_495_ = lean_ctor_get(v___x_489_, 4);
v_roundBudget_496_ = lean_ctor_get(v___x_489_, 5);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_507_ == 0)
{
v___x_498_ = v___x_489_;
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_roundBudget_496_);
lean_inc(v_solverTimeBudgetMs_495_);
lean_inc(v_theoryState_494_);
lean_inc(v_usedHyps_492_);
lean_inc(v_hypQueue_491_);
lean_inc(v_satExpr_490_);
lean_dec(v___x_489_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_array_push(v_hypQueue_491_, v_hyp_473_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_satExpr_490_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_usedHyps_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_theoryState_494_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_solverTimeBudgetMs_495_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_roundBudget_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*6, v_didChange_493_);
v___x_503_ = v_reuseFailAlloc_506_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_st_ref_put(v_a_475_, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_500_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___boxed(lean_object* v_hyp_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(v_hyp_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_usedHyps_528_; lean_object* v___x_529_; 
v___x_527_ = lean_st_ref_get(v_a_525_);
v_usedHyps_528_ = lean_ctor_get(v___x_527_, 2);
lean_inc_ref(v_usedHyps_528_);
lean_dec(v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_usedHyps_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg___boxed(lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(v_a_530_);
lean_dec(v_a_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; lean_object* v_usedHyps_549_; lean_object* v___x_550_; 
v___x_548_ = lean_st_ref_get(v_a_534_);
v_usedHyps_549_ = lean_ctor_get(v___x_548_, 2);
lean_inc_ref(v_usedHyps_549_);
lean_dec(v___x_548_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_usedHyps_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___boxed(lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_satExpr_572_; lean_object* v_hypQueue_573_; lean_object* v_usedHyps_574_; uint8_t v_didChange_575_; lean_object* v_theoryState_576_; lean_object* v_solverTimeBudgetMs_577_; lean_object* v_roundBudget_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_589_; 
v___x_571_ = lean_st_ref_take(v_a_569_);
v_satExpr_572_ = lean_ctor_get(v___x_571_, 0);
v_hypQueue_573_ = lean_ctor_get(v___x_571_, 1);
v_usedHyps_574_ = lean_ctor_get(v___x_571_, 2);
v_didChange_575_ = lean_ctor_get_uint8(v___x_571_, sizeof(void*)*6);
v_theoryState_576_ = lean_ctor_get(v___x_571_, 3);
v_solverTimeBudgetMs_577_ = lean_ctor_get(v___x_571_, 4);
v_roundBudget_578_ = lean_ctor_get(v___x_571_, 5);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_589_ == 0)
{
v___x_580_ = v___x_571_;
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_roundBudget_578_);
lean_inc(v_solverTimeBudgetMs_577_);
lean_inc(v_theoryState_576_);
lean_inc(v_usedHyps_574_);
lean_inc(v_hypQueue_573_);
lean_inc(v_satExpr_572_);
lean_dec(v___x_571_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_583_ = l_Array_append___redArg(v_usedHyps_574_, v_hypQueue_573_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v___x_583_);
lean_ctor_set(v___x_580_, 1, v___x_582_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_satExpr_572_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_theoryState_576_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_solverTimeBudgetMs_577_);
lean_ctor_set(v_reuseFailAlloc_588_, 5, v_roundBudget_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*6, v_didChange_575_);
v___x_585_ = v_reuseFailAlloc_588_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_st_ref_put(v_a_569_, v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_hypQueue_573_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___boxed(lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(v_a_590_);
lean_dec(v_a_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; lean_object* v_satExpr_609_; lean_object* v_hypQueue_610_; lean_object* v_usedHyps_611_; uint8_t v_didChange_612_; lean_object* v_theoryState_613_; lean_object* v_solverTimeBudgetMs_614_; lean_object* v_roundBudget_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_626_; 
v___x_608_ = lean_st_ref_take(v_a_594_);
v_satExpr_609_ = lean_ctor_get(v___x_608_, 0);
v_hypQueue_610_ = lean_ctor_get(v___x_608_, 1);
v_usedHyps_611_ = lean_ctor_get(v___x_608_, 2);
v_didChange_612_ = lean_ctor_get_uint8(v___x_608_, sizeof(void*)*6);
v_theoryState_613_ = lean_ctor_get(v___x_608_, 3);
v_solverTimeBudgetMs_614_ = lean_ctor_get(v___x_608_, 4);
v_roundBudget_615_ = lean_ctor_get(v___x_608_, 5);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_626_ == 0)
{
v___x_617_ = v___x_608_;
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_roundBudget_615_);
lean_inc(v_solverTimeBudgetMs_614_);
lean_inc(v_theoryState_613_);
lean_inc(v_usedHyps_611_);
lean_inc(v_hypQueue_610_);
lean_inc(v_satExpr_609_);
lean_dec(v___x_608_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_620_ = l_Array_append___redArg(v_usedHyps_611_, v_hypQueue_610_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 2, v___x_620_);
lean_ctor_set(v___x_617_, 1, v___x_619_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_satExpr_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_theoryState_613_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_solverTimeBudgetMs_614_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v_roundBudget_615_);
lean_ctor_set_uint8(v_reuseFailAlloc_625_, sizeof(void*)*6, v_didChange_612_);
v___x_622_ = v_reuseFailAlloc_625_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_st_ref_put(v_a_594_, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_hypQueue_610_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___boxed(lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(lean_object* v_a_643_){
_start:
{
lean_object* v_tacticContext_645_; lean_object* v___x_646_; 
v_tacticContext_645_ = lean_ctor_get(v_a_643_, 2);
lean_inc_ref(v_tacticContext_645_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_tacticContext_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg___boxed(lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(v_a_647_);
lean_dec_ref(v_a_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_tacticContext_665_; lean_object* v___x_666_; 
v_tacticContext_665_ = lean_ctor_get(v_a_650_, 2);
lean_inc_ref(v_tacticContext_665_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_tacticContext_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___boxed(lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(lean_object* v_a_683_){
_start:
{
lean_object* v_tacticContext_685_; lean_object* v_config_686_; uint8_t v_uf_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_tacticContext_685_ = lean_ctor_get(v_a_683_, 2);
v_config_686_ = lean_ctor_get(v_tacticContext_685_, 5);
v_uf_687_ = lean_ctor_get_uint8(v_config_686_, sizeof(void*)*3 + 11);
v___x_688_ = lean_box(v_uf_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg___boxed(lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(v_a_690_);
lean_dec_ref(v_a_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_tacticContext_708_; lean_object* v_config_709_; uint8_t v_uf_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_tacticContext_708_ = lean_ctor_get(v_a_693_, 2);
v_config_709_ = lean_ctor_get(v_tacticContext_708_, 5);
v_uf_710_ = lean_ctor_get_uint8(v_config_709_, sizeof(void*)*3 + 11);
v___x_711_ = lean_box(v_uf_710_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___boxed(lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(lean_object* v_ms_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; lean_object* v_satExpr_733_; lean_object* v_hypQueue_734_; lean_object* v_usedHyps_735_; uint8_t v_didChange_736_; lean_object* v_theoryState_737_; lean_object* v_solverTimeBudgetMs_738_; lean_object* v_roundBudget_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_750_; 
v___x_732_ = lean_st_ref_take(v_a_730_);
v_satExpr_733_ = lean_ctor_get(v___x_732_, 0);
v_hypQueue_734_ = lean_ctor_get(v___x_732_, 1);
v_usedHyps_735_ = lean_ctor_get(v___x_732_, 2);
v_didChange_736_ = lean_ctor_get_uint8(v___x_732_, sizeof(void*)*6);
v_theoryState_737_ = lean_ctor_get(v___x_732_, 3);
v_solverTimeBudgetMs_738_ = lean_ctor_get(v___x_732_, 4);
v_roundBudget_739_ = lean_ctor_get(v___x_732_, 5);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_741_ = v___x_732_;
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_roundBudget_739_);
lean_inc(v_solverTimeBudgetMs_738_);
lean_inc(v_theoryState_737_);
lean_inc(v_usedHyps_735_);
lean_inc(v_hypQueue_734_);
lean_inc(v_satExpr_733_);
lean_dec(v___x_732_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = lean_box(0);
v___x_744_ = lean_nat_sub(v_solverTimeBudgetMs_738_, v_ms_729_);
lean_dec(v_solverTimeBudgetMs_738_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 4, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_satExpr_733_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_hypQueue_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_usedHyps_735_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_theoryState_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v_roundBudget_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_749_, sizeof(void*)*6, v_didChange_736_);
v___x_746_ = v_reuseFailAlloc_749_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_st_ref_put(v_a_730_, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_743_);
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg___boxed(lean_object* v_ms_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(v_ms_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec(v_ms_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(lean_object* v_ms_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_satExpr_772_; lean_object* v_hypQueue_773_; lean_object* v_usedHyps_774_; uint8_t v_didChange_775_; lean_object* v_theoryState_776_; lean_object* v_solverTimeBudgetMs_777_; lean_object* v_roundBudget_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v___x_771_ = lean_st_ref_take(v_a_757_);
v_satExpr_772_ = lean_ctor_get(v___x_771_, 0);
v_hypQueue_773_ = lean_ctor_get(v___x_771_, 1);
v_usedHyps_774_ = lean_ctor_get(v___x_771_, 2);
v_didChange_775_ = lean_ctor_get_uint8(v___x_771_, sizeof(void*)*6);
v_theoryState_776_ = lean_ctor_get(v___x_771_, 3);
v_solverTimeBudgetMs_777_ = lean_ctor_get(v___x_771_, 4);
v_roundBudget_778_ = lean_ctor_get(v___x_771_, 5);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v___x_771_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_roundBudget_778_);
lean_inc(v_solverTimeBudgetMs_777_);
lean_inc(v_theoryState_776_);
lean_inc(v_usedHyps_774_);
lean_inc(v_hypQueue_773_);
lean_inc(v_satExpr_772_);
lean_dec(v___x_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_box(0);
v___x_783_ = lean_nat_sub(v_solverTimeBudgetMs_777_, v_ms_755_);
lean_dec(v_solverTimeBudgetMs_777_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_satExpr_772_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_hypQueue_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_usedHyps_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_theoryState_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_788_, 5, v_roundBudget_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_788_, sizeof(void*)*6, v_didChange_775_);
v___x_785_ = v_reuseFailAlloc_788_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_st_ref_put(v_a_757_, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___boxed(lean_object* v_ms_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(v_ms_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_ms_790_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; lean_object* v_solverTimeBudgetMs_810_; lean_object* v___x_811_; 
v___x_809_ = lean_st_ref_get(v_a_807_);
v_solverTimeBudgetMs_810_ = lean_ctor_get(v___x_809_, 4);
lean_inc(v_solverTimeBudgetMs_810_);
lean_dec(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_solverTimeBudgetMs_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg___boxed(lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(v_a_812_);
lean_dec(v_a_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_solverTimeBudgetMs_831_; lean_object* v___x_832_; 
v___x_830_ = lean_st_ref_get(v_a_816_);
v_solverTimeBudgetMs_831_ = lean_ctor_get(v___x_830_, 4);
lean_inc(v_solverTimeBudgetMs_831_);
lean_dec(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_solverTimeBudgetMs_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___boxed(lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_satExpr_852_; lean_object* v_hypQueue_853_; lean_object* v_usedHyps_854_; uint8_t v_didChange_855_; lean_object* v_theoryState_856_; lean_object* v_solverTimeBudgetMs_857_; lean_object* v_roundBudget_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_870_; 
v___x_851_ = lean_st_ref_take(v_a_849_);
v_satExpr_852_ = lean_ctor_get(v___x_851_, 0);
v_hypQueue_853_ = lean_ctor_get(v___x_851_, 1);
v_usedHyps_854_ = lean_ctor_get(v___x_851_, 2);
v_didChange_855_ = lean_ctor_get_uint8(v___x_851_, sizeof(void*)*6);
v_theoryState_856_ = lean_ctor_get(v___x_851_, 3);
v_solverTimeBudgetMs_857_ = lean_ctor_get(v___x_851_, 4);
v_roundBudget_858_ = lean_ctor_get(v___x_851_, 5);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_870_ == 0)
{
v___x_860_ = v___x_851_;
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_roundBudget_858_);
lean_inc(v_solverTimeBudgetMs_857_);
lean_inc(v_theoryState_856_);
lean_inc(v_usedHyps_854_);
lean_inc(v_hypQueue_853_);
lean_inc(v_satExpr_852_);
lean_dec(v___x_851_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_sub(v_roundBudget_858_, v___x_863_);
lean_dec(v_roundBudget_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 5, v___x_864_);
v___x_866_ = v___x_860_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_satExpr_852_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_hypQueue_853_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_usedHyps_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_theoryState_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_solverTimeBudgetMs_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v___x_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*6, v_didChange_855_);
v___x_866_ = v_reuseFailAlloc_869_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_st_ref_put(v_a_849_, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_862_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg___boxed(lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(v_a_871_);
lean_dec(v_a_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_889_; lean_object* v_satExpr_890_; lean_object* v_hypQueue_891_; lean_object* v_usedHyps_892_; uint8_t v_didChange_893_; lean_object* v_theoryState_894_; lean_object* v_solverTimeBudgetMs_895_; lean_object* v_roundBudget_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_908_; 
v___x_889_ = lean_st_ref_take(v_a_875_);
v_satExpr_890_ = lean_ctor_get(v___x_889_, 0);
v_hypQueue_891_ = lean_ctor_get(v___x_889_, 1);
v_usedHyps_892_ = lean_ctor_get(v___x_889_, 2);
v_didChange_893_ = lean_ctor_get_uint8(v___x_889_, sizeof(void*)*6);
v_theoryState_894_ = lean_ctor_get(v___x_889_, 3);
v_solverTimeBudgetMs_895_ = lean_ctor_get(v___x_889_, 4);
v_roundBudget_896_ = lean_ctor_get(v___x_889_, 5);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_908_ == 0)
{
v___x_898_ = v___x_889_;
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_roundBudget_896_);
lean_inc(v_solverTimeBudgetMs_895_);
lean_inc(v_theoryState_894_);
lean_inc(v_usedHyps_892_);
lean_inc(v_hypQueue_891_);
lean_inc(v_satExpr_890_);
lean_dec(v___x_889_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_sub(v_roundBudget_896_, v___x_901_);
lean_dec(v_roundBudget_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 5, v___x_902_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_satExpr_890_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_hypQueue_891_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_usedHyps_892_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_theoryState_894_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_solverTimeBudgetMs_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 5, v___x_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*6, v_didChange_893_);
v___x_904_ = v_reuseFailAlloc_907_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_st_ref_put(v_a_875_, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_900_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___boxed(lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v_roundBudget_928_; lean_object* v___x_929_; 
v___x_927_ = lean_st_ref_get(v_a_925_);
v_roundBudget_928_ = lean_ctor_get(v___x_927_, 5);
lean_inc(v_roundBudget_928_);
lean_dec(v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v_roundBudget_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg___boxed(lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(v_a_930_);
lean_dec(v_a_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_roundBudget_949_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_get(v_a_934_);
v_roundBudget_949_ = lean_ctor_get(v___x_948_, 5);
lean_inc(v_roundBudget_949_);
lean_dec(v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_roundBudget_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___boxed(lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_theoryState_970_; lean_object* v_satExpr_971_; lean_object* v_hypQueue_972_; lean_object* v_usedHyps_973_; uint8_t v_didChange_974_; lean_object* v_solverTimeBudgetMs_975_; lean_object* v_roundBudget_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_997_; 
v___x_969_ = lean_st_ref_take(v_a_967_);
v_theoryState_970_ = lean_ctor_get(v___x_969_, 3);
v_satExpr_971_ = lean_ctor_get(v___x_969_, 0);
v_hypQueue_972_ = lean_ctor_get(v___x_969_, 1);
v_usedHyps_973_ = lean_ctor_get(v___x_969_, 2);
v_didChange_974_ = lean_ctor_get_uint8(v___x_969_, sizeof(void*)*6);
v_solverTimeBudgetMs_975_ = lean_ctor_get(v___x_969_, 4);
v_roundBudget_976_ = lean_ctor_get(v___x_969_, 5);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_997_ == 0)
{
v___x_978_ = v___x_969_;
v_isShared_979_ = v_isSharedCheck_997_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_roundBudget_976_);
lean_inc(v_solverTimeBudgetMs_975_);
lean_inc(v_theoryState_970_);
lean_inc(v_usedHyps_973_);
lean_inc(v_hypQueue_972_);
lean_inc(v_satExpr_971_);
lean_dec(v___x_969_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_997_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_funState_980_; lean_object* v_bitvecState_981_; lean_object* v_preprocessCaches_982_; lean_object* v_satSolver_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_996_; 
v_funState_980_ = lean_ctor_get(v_theoryState_970_, 0);
v_bitvecState_981_ = lean_ctor_get(v_theoryState_970_, 1);
v_preprocessCaches_982_ = lean_ctor_get(v_theoryState_970_, 2);
v_satSolver_983_ = lean_ctor_get(v_theoryState_970_, 3);
v_isSharedCheck_996_ = !lean_is_exclusive(v_theoryState_970_);
if (v_isSharedCheck_996_ == 0)
{
v___x_985_ = v_theoryState_970_;
v_isShared_986_ = v_isSharedCheck_996_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_satSolver_983_);
lean_inc(v_preprocessCaches_982_);
lean_inc(v_bitvecState_981_);
lean_inc(v_funState_980_);
lean_dec(v_theoryState_970_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_996_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 2, v___x_987_);
v___x_989_ = v___x_985_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_funState_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_bitvecState_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_satSolver_983_);
v___x_989_ = v_reuseFailAlloc_995_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 3, v___x_989_);
v___x_991_ = v___x_978_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_satExpr_971_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_hypQueue_972_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_usedHyps_973_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_solverTimeBudgetMs_975_);
lean_ctor_set(v_reuseFailAlloc_994_, 5, v_roundBudget_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*6, v_didChange_974_);
v___x_991_ = v_reuseFailAlloc_994_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_st_ref_put(v_a_967_, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_preprocessCaches_982_);
return v___x_993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg___boxed(lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(v_a_998_);
lean_dec(v_a_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v_theoryState_1017_; lean_object* v_satExpr_1018_; lean_object* v_hypQueue_1019_; lean_object* v_usedHyps_1020_; uint8_t v_didChange_1021_; lean_object* v_solverTimeBudgetMs_1022_; lean_object* v_roundBudget_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1044_; 
v___x_1016_ = lean_st_ref_take(v_a_1002_);
v_theoryState_1017_ = lean_ctor_get(v___x_1016_, 3);
v_satExpr_1018_ = lean_ctor_get(v___x_1016_, 0);
v_hypQueue_1019_ = lean_ctor_get(v___x_1016_, 1);
v_usedHyps_1020_ = lean_ctor_get(v___x_1016_, 2);
v_didChange_1021_ = lean_ctor_get_uint8(v___x_1016_, sizeof(void*)*6);
v_solverTimeBudgetMs_1022_ = lean_ctor_get(v___x_1016_, 4);
v_roundBudget_1023_ = lean_ctor_get(v___x_1016_, 5);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1025_ = v___x_1016_;
v_isShared_1026_ = v_isSharedCheck_1044_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_roundBudget_1023_);
lean_inc(v_solverTimeBudgetMs_1022_);
lean_inc(v_theoryState_1017_);
lean_inc(v_usedHyps_1020_);
lean_inc(v_hypQueue_1019_);
lean_inc(v_satExpr_1018_);
lean_dec(v___x_1016_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1044_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_funState_1027_; lean_object* v_bitvecState_1028_; lean_object* v_preprocessCaches_1029_; lean_object* v_satSolver_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1043_; 
v_funState_1027_ = lean_ctor_get(v_theoryState_1017_, 0);
v_bitvecState_1028_ = lean_ctor_get(v_theoryState_1017_, 1);
v_preprocessCaches_1029_ = lean_ctor_get(v_theoryState_1017_, 2);
v_satSolver_1030_ = lean_ctor_get(v_theoryState_1017_, 3);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_theoryState_1017_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1032_ = v_theoryState_1017_;
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_satSolver_1030_);
lean_inc(v_preprocessCaches_1029_);
lean_inc(v_bitvecState_1028_);
lean_inc(v_funState_1027_);
lean_dec(v_theoryState_1017_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 2, v___x_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_funState_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_bitvecState_1028_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_satSolver_1030_);
v___x_1036_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 3, v___x_1036_);
v___x_1038_ = v___x_1025_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_satExpr_1018_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_hypQueue_1019_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_usedHyps_1020_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_solverTimeBudgetMs_1022_);
lean_ctor_set(v_reuseFailAlloc_1041_, 5, v_roundBudget_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*6, v_didChange_1021_);
v___x_1038_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_st_ref_put(v_a_1002_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_preprocessCaches_1029_);
return v___x_1040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___boxed(lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(lean_object* v_caches_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v_theoryState_1065_; lean_object* v_satExpr_1066_; lean_object* v_hypQueue_1067_; lean_object* v_usedHyps_1068_; uint8_t v_didChange_1069_; lean_object* v_solverTimeBudgetMs_1070_; lean_object* v_roundBudget_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1092_; 
v___x_1064_ = lean_st_ref_take(v_a_1062_);
v_theoryState_1065_ = lean_ctor_get(v___x_1064_, 3);
v_satExpr_1066_ = lean_ctor_get(v___x_1064_, 0);
v_hypQueue_1067_ = lean_ctor_get(v___x_1064_, 1);
v_usedHyps_1068_ = lean_ctor_get(v___x_1064_, 2);
v_didChange_1069_ = lean_ctor_get_uint8(v___x_1064_, sizeof(void*)*6);
v_solverTimeBudgetMs_1070_ = lean_ctor_get(v___x_1064_, 4);
v_roundBudget_1071_ = lean_ctor_get(v___x_1064_, 5);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1073_ = v___x_1064_;
v_isShared_1074_ = v_isSharedCheck_1092_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_roundBudget_1071_);
lean_inc(v_solverTimeBudgetMs_1070_);
lean_inc(v_theoryState_1065_);
lean_inc(v_usedHyps_1068_);
lean_inc(v_hypQueue_1067_);
lean_inc(v_satExpr_1066_);
lean_dec(v___x_1064_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1092_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_funState_1075_; lean_object* v_bitvecState_1076_; lean_object* v_satSolver_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1090_; 
v_funState_1075_ = lean_ctor_get(v_theoryState_1065_, 0);
v_bitvecState_1076_ = lean_ctor_get(v_theoryState_1065_, 1);
v_satSolver_1077_ = lean_ctor_get(v_theoryState_1065_, 3);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_theoryState_1065_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_theoryState_1065_, 2);
lean_dec(v_unused_1091_);
v___x_1079_ = v_theoryState_1065_;
v_isShared_1080_ = v_isSharedCheck_1090_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_satSolver_1077_);
lean_inc(v_bitvecState_1076_);
lean_inc(v_funState_1075_);
lean_dec(v_theoryState_1065_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1090_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 2, v_caches_1061_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_funState_1075_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_bitvecState_1076_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_caches_1061_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_satSolver_1077_);
v___x_1083_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 3, v___x_1083_);
v___x_1085_ = v___x_1073_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_satExpr_1066_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_hypQueue_1067_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_usedHyps_1068_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_solverTimeBudgetMs_1070_);
lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_roundBudget_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*6, v_didChange_1069_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_st_ref_put(v_a_1062_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1081_);
return v___x_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg___boxed(lean_object* v_caches_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(v_caches_1093_, v_a_1094_);
lean_dec(v_a_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(lean_object* v_caches_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_theoryState_1114_; lean_object* v_satExpr_1115_; lean_object* v_hypQueue_1116_; lean_object* v_usedHyps_1117_; uint8_t v_didChange_1118_; lean_object* v_solverTimeBudgetMs_1119_; lean_object* v_roundBudget_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1141_; 
v___x_1113_ = lean_st_ref_take(v_a_1099_);
v_theoryState_1114_ = lean_ctor_get(v___x_1113_, 3);
v_satExpr_1115_ = lean_ctor_get(v___x_1113_, 0);
v_hypQueue_1116_ = lean_ctor_get(v___x_1113_, 1);
v_usedHyps_1117_ = lean_ctor_get(v___x_1113_, 2);
v_didChange_1118_ = lean_ctor_get_uint8(v___x_1113_, sizeof(void*)*6);
v_solverTimeBudgetMs_1119_ = lean_ctor_get(v___x_1113_, 4);
v_roundBudget_1120_ = lean_ctor_get(v___x_1113_, 5);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1122_ = v___x_1113_;
v_isShared_1123_ = v_isSharedCheck_1141_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_roundBudget_1120_);
lean_inc(v_solverTimeBudgetMs_1119_);
lean_inc(v_theoryState_1114_);
lean_inc(v_usedHyps_1117_);
lean_inc(v_hypQueue_1116_);
lean_inc(v_satExpr_1115_);
lean_dec(v___x_1113_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1141_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_funState_1124_; lean_object* v_bitvecState_1125_; lean_object* v_satSolver_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1139_; 
v_funState_1124_ = lean_ctor_get(v_theoryState_1114_, 0);
v_bitvecState_1125_ = lean_ctor_get(v_theoryState_1114_, 1);
v_satSolver_1126_ = lean_ctor_get(v_theoryState_1114_, 3);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_theoryState_1114_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v_theoryState_1114_, 2);
lean_dec(v_unused_1140_);
v___x_1128_ = v_theoryState_1114_;
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_satSolver_1126_);
lean_inc(v_bitvecState_1125_);
lean_inc(v_funState_1124_);
lean_dec(v_theoryState_1114_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_box(0);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v_caches_1097_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_funState_1124_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_bitvecState_1125_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_caches_1097_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_satSolver_1126_);
v___x_1132_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 3, v___x_1132_);
v___x_1134_ = v___x_1122_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_satExpr_1115_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_hypQueue_1116_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_usedHyps_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_solverTimeBudgetMs_1119_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_roundBudget_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1137_, sizeof(void*)*6, v_didChange_1118_);
v___x_1134_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_st_ref_put(v_a_1099_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1130_);
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___boxed(lean_object* v_caches_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(v_caches_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(lean_object* v_ctx_1159_, lean_object* v_x_1160_, lean_object* v_goal_1161_, lean_object* v_reflectionResult_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v_config_1177_; lean_object* v_satExpr_1178_; lean_object* v_unusedHypotheses_1179_; lean_object* v_timeout_1180_; lean_object* v_cegarRounds_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1176_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1177_ = lean_ctor_get(v_ctx_1159_, 5);
v_satExpr_1178_ = lean_ctor_get(v_reflectionResult_1162_, 0);
v_unusedHypotheses_1179_ = lean_ctor_get(v_reflectionResult_1162_, 1);
v_timeout_1180_ = lean_ctor_get(v_config_1177_, 0);
v_cegarRounds_1181_ = lean_ctor_get(v_config_1177_, 2);
v___x_1182_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1183_ = 1;
v___x_1184_ = lean_unsigned_to_nat(1000u);
v___x_1185_ = lean_nat_mul(v_timeout_1180_, v___x_1184_);
lean_inc(v_cegarRounds_1181_);
lean_inc_ref(v_satExpr_1178_);
v___x_1186_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1186_, 0, v_satExpr_1178_);
lean_ctor_set(v___x_1186_, 1, v___x_1182_);
lean_ctor_set(v___x_1186_, 2, v___x_1182_);
lean_ctor_set(v___x_1186_, 3, v___x_1176_);
lean_ctor_set(v___x_1186_, 4, v___x_1185_);
lean_ctor_set(v___x_1186_, 5, v_cegarRounds_1181_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*6, v___x_1183_);
lean_inc_ref(v_unusedHypotheses_1179_);
v___x_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1187_, 0, v_goal_1161_);
lean_ctor_set(v___x_1187_, 1, v_unusedHypotheses_1179_);
lean_ctor_set(v___x_1187_, 2, v_ctx_1159_);
v___x_1188_ = lean_st_mk_ref(v___x_1186_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
lean_inc_ref(v_a_1171_);
lean_inc(v_a_1170_);
lean_inc_ref(v_a_1169_);
lean_inc(v_a_1168_);
lean_inc_ref(v_a_1167_);
lean_inc(v_a_1166_);
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
lean_inc(v_a_1163_);
lean_inc(v___x_1188_);
v___x_1189_ = lean_apply_15(v_x_1160_, v___x_1187_, v___x_1188_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, lean_box(0));
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_st_ref_get(v___x_1188_);
lean_dec(v___x_1188_);
lean_dec(v___x_1194_);
if (v_isShared_1193_ == 0)
{
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1190_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_dec(v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg___boxed(lean_object** _args){
lean_object* v_ctx_1199_ = _args[0];
lean_object* v_x_1200_ = _args[1];
lean_object* v_goal_1201_ = _args[2];
lean_object* v_reflectionResult_1202_ = _args[3];
lean_object* v_a_1203_ = _args[4];
lean_object* v_a_1204_ = _args[5];
lean_object* v_a_1205_ = _args[6];
lean_object* v_a_1206_ = _args[7];
lean_object* v_a_1207_ = _args[8];
lean_object* v_a_1208_ = _args[9];
lean_object* v_a_1209_ = _args[10];
lean_object* v_a_1210_ = _args[11];
lean_object* v_a_1211_ = _args[12];
lean_object* v_a_1212_ = _args[13];
lean_object* v_a_1213_ = _args[14];
lean_object* v_a_1214_ = _args[15];
lean_object* v_a_1215_ = _args[16];
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(v_ctx_1199_, v_x_1200_, v_goal_1201_, v_reflectionResult_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_reflectionResult_1202_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_object* v_00_u03b1_1217_, lean_object* v_ctx_1218_, lean_object* v_x_1219_, lean_object* v_goal_1220_, lean_object* v_reflectionResult_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_config_1236_; lean_object* v_satExpr_1237_; lean_object* v_unusedHypotheses_1238_; lean_object* v_timeout_1239_; lean_object* v_cegarRounds_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1235_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1236_ = lean_ctor_get(v_ctx_1218_, 5);
v_satExpr_1237_ = lean_ctor_get(v_reflectionResult_1221_, 0);
v_unusedHypotheses_1238_ = lean_ctor_get(v_reflectionResult_1221_, 1);
v_timeout_1239_ = lean_ctor_get(v_config_1236_, 0);
v_cegarRounds_1240_ = lean_ctor_get(v_config_1236_, 2);
v___x_1241_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1242_ = 1;
v___x_1243_ = lean_unsigned_to_nat(1000u);
v___x_1244_ = lean_nat_mul(v_timeout_1239_, v___x_1243_);
lean_inc(v_cegarRounds_1240_);
lean_inc_ref(v_satExpr_1237_);
v___x_1245_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1245_, 0, v_satExpr_1237_);
lean_ctor_set(v___x_1245_, 1, v___x_1241_);
lean_ctor_set(v___x_1245_, 2, v___x_1241_);
lean_ctor_set(v___x_1245_, 3, v___x_1235_);
lean_ctor_set(v___x_1245_, 4, v___x_1244_);
lean_ctor_set(v___x_1245_, 5, v_cegarRounds_1240_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*6, v___x_1242_);
lean_inc_ref(v_unusedHypotheses_1238_);
v___x_1246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1246_, 0, v_goal_1220_);
lean_ctor_set(v___x_1246_, 1, v_unusedHypotheses_1238_);
lean_ctor_set(v___x_1246_, 2, v_ctx_1218_);
v___x_1247_ = lean_st_mk_ref(v___x_1245_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc_ref(v_a_1223_);
lean_inc(v_a_1222_);
lean_inc(v___x_1247_);
v___x_1248_ = lean_apply_15(v_x_1219_, v___x_1246_, v___x_1247_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1257_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_st_ref_get(v___x_1247_);
lean_dec(v___x_1247_);
lean_dec(v___x_1253_);
if (v_isShared_1252_ == 0)
{
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1249_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_dec(v___x_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___boxed(lean_object** _args){
lean_object* v_00_u03b1_1258_ = _args[0];
lean_object* v_ctx_1259_ = _args[1];
lean_object* v_x_1260_ = _args[2];
lean_object* v_goal_1261_ = _args[3];
lean_object* v_reflectionResult_1262_ = _args[4];
lean_object* v_a_1263_ = _args[5];
lean_object* v_a_1264_ = _args[6];
lean_object* v_a_1265_ = _args[7];
lean_object* v_a_1266_ = _args[8];
lean_object* v_a_1267_ = _args[9];
lean_object* v_a_1268_ = _args[10];
lean_object* v_a_1269_ = _args[11];
lean_object* v_a_1270_ = _args[12];
lean_object* v_a_1271_ = _args[13];
lean_object* v_a_1272_ = _args[14];
lean_object* v_a_1273_ = _args[15];
lean_object* v_a_1274_ = _args[16];
lean_object* v_a_1275_ = _args[17];
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run(v_00_u03b1_1258_, v_ctx_1259_, v_x_1260_, v_goal_1261_, v_reflectionResult_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_reflectionResult_1262_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_theoryState_1280_; lean_object* v_satSolver_1281_; lean_object* v___x_1282_; 
v___x_1279_ = lean_st_ref_get(v_a_1277_);
v_theoryState_1280_ = lean_ctor_get(v___x_1279_, 3);
lean_inc_ref(v_theoryState_1280_);
lean_dec(v___x_1279_);
v_satSolver_1281_ = lean_ctor_get(v_theoryState_1280_, 3);
lean_inc_ref(v_satSolver_1281_);
lean_dec_ref(v_theoryState_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_satSolver_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg___boxed(lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1283_);
lean_dec(v_a_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1287_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___boxed(lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1317_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_instMonadEIO___redArg();
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(lean_object* v_msg_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_toApplicative_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1406_; 
v___x_1336_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0);
v___x_1337_ = l_StateRefT_x27_instMonad___redArg(v___x_1336_);
v_toApplicative_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1337_, 1);
lean_dec(v_unused_1407_);
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1406_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_toApplicative_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1406_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_toFunctor_1342_; lean_object* v_toSeq_1343_; lean_object* v_toSeqLeft_1344_; lean_object* v_toSeqRight_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1404_; 
v_toFunctor_1342_ = lean_ctor_get(v_toApplicative_1338_, 0);
v_toSeq_1343_ = lean_ctor_get(v_toApplicative_1338_, 2);
v_toSeqLeft_1344_ = lean_ctor_get(v_toApplicative_1338_, 3);
v_toSeqRight_1345_ = lean_ctor_get(v_toApplicative_1338_, 4);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_toApplicative_1338_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_toApplicative_1338_, 1);
lean_dec(v_unused_1405_);
v___x_1347_ = v_toApplicative_1338_;
v_isShared_1348_ = v_isSharedCheck_1404_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_toSeqRight_1345_);
lean_inc(v_toSeqLeft_1344_);
lean_inc(v_toSeq_1343_);
lean_inc(v_toFunctor_1342_);
lean_dec(v_toApplicative_1338_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1404_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___f_1349_; lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___f_1356_; lean_object* v___x_1358_; 
v___f_1349_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1));
v___f_1350_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1342_);
v___f_1351_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1351_, 0, v_toFunctor_1342_);
v___f_1352_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1352_, 0, v_toFunctor_1342_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___f_1351_);
lean_ctor_set(v___x_1353_, 1, v___f_1352_);
v___f_1354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1354_, 0, v_toSeqRight_1345_);
v___f_1355_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1355_, 0, v_toSeqLeft_1344_);
v___f_1356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1356_, 0, v_toSeq_1343_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 4, v___f_1354_);
lean_ctor_set(v___x_1347_, 3, v___f_1355_);
lean_ctor_set(v___x_1347_, 2, v___f_1356_);
lean_ctor_set(v___x_1347_, 1, v___f_1349_);
lean_ctor_set(v___x_1347_, 0, v___x_1353_);
v___x_1358_ = v___x_1347_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___f_1349_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v___f_1356_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___f_1355_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v___f_1354_);
v___x_1358_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___f_1350_);
lean_ctor_set(v___x_1340_, 0, v___x_1358_);
v___x_1360_ = v___x_1340_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___f_1350_);
v___x_1360_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v_toApplicative_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1400_; 
v___x_1361_ = l_StateRefT_x27_instMonad___redArg(v___x_1360_);
v_toApplicative_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1361_, 1);
lean_dec(v_unused_1401_);
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1400_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_toApplicative_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1400_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_toFunctor_1366_; lean_object* v_toSeq_1367_; lean_object* v_toSeqLeft_1368_; lean_object* v_toSeqRight_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1398_; 
v_toFunctor_1366_ = lean_ctor_get(v_toApplicative_1362_, 0);
v_toSeq_1367_ = lean_ctor_get(v_toApplicative_1362_, 2);
v_toSeqLeft_1368_ = lean_ctor_get(v_toApplicative_1362_, 3);
v_toSeqRight_1369_ = lean_ctor_get(v_toApplicative_1362_, 4);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_toApplicative_1362_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v_toApplicative_1362_, 1);
lean_dec(v_unused_1399_);
v___x_1371_ = v_toApplicative_1362_;
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_toSeqRight_1369_);
lean_inc(v_toSeqLeft_1368_);
lean_inc(v_toSeq_1367_);
lean_inc(v_toFunctor_1366_);
lean_dec(v_toApplicative_1362_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1398_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___f_1373_; lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___f_1380_; lean_object* v___x_1382_; 
v___f_1373_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3));
v___f_1374_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4));
lean_inc_ref(v_toFunctor_1366_);
v___f_1375_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1375_, 0, v_toFunctor_1366_);
v___f_1376_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1376_, 0, v_toFunctor_1366_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___f_1375_);
lean_ctor_set(v___x_1377_, 1, v___f_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1378_, 0, v_toSeqRight_1369_);
v___f_1379_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1379_, 0, v_toSeqLeft_1368_);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toSeq_1367_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___f_1378_);
lean_ctor_set(v___x_1371_, 3, v___f_1379_);
lean_ctor_set(v___x_1371_, 2, v___f_1380_);
lean_ctor_set(v___x_1371_, 1, v___f_1373_);
lean_ctor_set(v___x_1371_, 0, v___x_1377_);
v___x_1382_ = v___x_1371_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___f_1373_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v___f_1380_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v___f_1379_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v___f_1378_);
v___x_1382_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___f_1374_);
lean_ctor_set(v___x_1364_, 0, v___x_1382_);
v___x_1384_ = v___x_1364_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___f_1374_);
v___x_1384_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___x_4587__overap_1394_; lean_object* v___x_1395_; 
v___x_1385_ = l_StateRefT_x27_instMonad___redArg(v___x_1384_);
v___x_1386_ = l_ReaderT_instMonad___redArg(v___x_1385_);
v___x_1387_ = l_StateRefT_x27_instMonad___redArg(v___x_1386_);
v___x_1388_ = l_ReaderT_instMonad___redArg(v___x_1387_);
v___x_1389_ = l_ReaderT_instMonad___redArg(v___x_1388_);
v___x_1390_ = l_StateRefT_x27_instMonad___redArg(v___x_1389_);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_instInhabitedOfMonad___redArg(v___x_1390_, v___x_1391_);
v___f_1393_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1393_, 0, v___x_1392_);
v___x_4587__overap_1394_ = lean_panic_fn_borrowed(v___f_1393_, v_msg_1323_);
lean_dec_ref(v___f_1393_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
v___x_1395_ = lean_apply_12(v___x_4587__overap_1394_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, lean_box(0));
return v___x_1395_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___boxed(lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
return v_x_1422_;
}
else
{
lean_object* v_key_1424_; lean_object* v_value_1425_; lean_object* v_tail_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1449_; 
v_key_1424_ = lean_ctor_get(v_x_1423_, 0);
v_value_1425_ = lean_ctor_get(v_x_1423_, 1);
v_tail_1426_ = lean_ctor_get(v_x_1423_, 2);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1423_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1428_ = v_x_1423_;
v_isShared_1429_ = v_isSharedCheck_1449_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_tail_1426_);
lean_inc(v_value_1425_);
lean_inc(v_key_1424_);
lean_dec(v_x_1423_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1449_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; uint64_t v___x_1431_; uint64_t v___x_1432_; uint64_t v___x_1433_; uint64_t v_fold_1434_; uint64_t v___x_1435_; uint64_t v___x_1436_; uint64_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1430_ = lean_array_get_size(v_x_1422_);
v___x_1431_ = l_Lean_Expr_hash(v_key_1424_);
v___x_1432_ = 32ULL;
v___x_1433_ = lean_uint64_shift_right(v___x_1431_, v___x_1432_);
v_fold_1434_ = lean_uint64_xor(v___x_1431_, v___x_1433_);
v___x_1435_ = 16ULL;
v___x_1436_ = lean_uint64_shift_right(v_fold_1434_, v___x_1435_);
v___x_1437_ = lean_uint64_xor(v_fold_1434_, v___x_1436_);
v___x_1438_ = lean_uint64_to_usize(v___x_1437_);
v___x_1439_ = lean_usize_of_nat(v___x_1430_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_sub(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_usize_land(v___x_1438_, v___x_1441_);
v___x_1443_ = lean_array_uget_borrowed(v_x_1422_, v___x_1442_);
lean_inc(v___x_1443_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 2, v___x_1443_);
v___x_1445_ = v___x_1428_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_key_1424_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_value_1425_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_array_uset(v_x_1422_, v___x_1442_, v___x_1445_);
v_x_1422_ = v___x_1446_;
v_x_1423_ = v_tail_1426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(lean_object* v_i_1450_, lean_object* v_source_1451_, lean_object* v_target_1452_){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_array_get_size(v_source_1451_);
v___x_1454_ = lean_nat_dec_lt(v_i_1450_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v_source_1451_);
lean_dec(v_i_1450_);
return v_target_1452_;
}
else
{
lean_object* v_es_1455_; lean_object* v___x_1456_; lean_object* v_source_1457_; lean_object* v_target_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_es_1455_ = lean_array_fget(v_source_1451_, v_i_1450_);
v___x_1456_ = lean_box(0);
v_source_1457_ = lean_array_fset(v_source_1451_, v_i_1450_, v___x_1456_);
v_target_1458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_target_1452_, v_es_1455_);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_i_1450_, v___x_1459_);
lean_dec(v_i_1450_);
v_i_1450_ = v___x_1460_;
v_source_1451_ = v_source_1457_;
v_target_1452_ = v_target_1458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(lean_object* v_data_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_nbuckets_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1463_ = lean_array_get_size(v_data_1462_);
v___x_1464_ = lean_unsigned_to_nat(2u);
v_nbuckets_1465_ = lean_nat_mul(v___x_1463_, v___x_1464_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_mk_array(v_nbuckets_1465_, v___x_1467_);
v___x_1469_ = lean_array_propagate_mark(v_data_1462_, v___x_1468_);
v___x_1470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v___x_1466_, v_data_1462_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(lean_object* v_a_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
uint8_t v___x_1473_; 
v___x_1473_ = 0;
return v___x_1473_;
}
else
{
lean_object* v_key_1474_; lean_object* v_tail_1475_; uint8_t v___x_1476_; 
v_key_1474_ = lean_ctor_get(v_x_1472_, 0);
v_tail_1475_ = lean_ctor_get(v_x_1472_, 2);
v___x_1476_ = lean_expr_eqv(v_key_1474_, v_a_1471_);
if (v___x_1476_ == 0)
{
v_x_1472_ = v_tail_1475_;
goto _start;
}
else
{
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg___boxed(lean_object* v_a_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1478_, v_x_1479_);
lean_dec(v_x_1479_);
lean_dec_ref(v_a_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(lean_object* v_a_1482_, lean_object* v_b_1483_, lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
lean_dec(v_b_1483_);
lean_dec_ref(v_a_1482_);
return v_x_1484_;
}
else
{
lean_object* v_key_1485_; lean_object* v_value_1486_; lean_object* v_tail_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1499_; 
v_key_1485_ = lean_ctor_get(v_x_1484_, 0);
v_value_1486_ = lean_ctor_get(v_x_1484_, 1);
v_tail_1487_ = lean_ctor_get(v_x_1484_, 2);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_x_1484_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1489_ = v_x_1484_;
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_tail_1487_);
lean_inc(v_value_1486_);
lean_inc(v_key_1485_);
lean_dec(v_x_1484_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_expr_eqv(v_key_1485_, v_a_1482_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1482_, v_b_1483_, v_tail_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 2, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_key_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_value_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
else
{
lean_object* v___x_1497_; 
lean_dec(v_value_1486_);
lean_dec(v_key_1485_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_b_1483_);
lean_ctor_set(v___x_1489_, 0, v_a_1482_);
v___x_1497_ = v___x_1489_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1482_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_b_1483_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_tail_1487_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(lean_object* v_m_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_){
_start:
{
lean_object* v_size_1503_; lean_object* v_buckets_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1547_; 
v_size_1503_ = lean_ctor_get(v_m_1500_, 0);
v_buckets_1504_ = lean_ctor_get(v_m_1500_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_m_1500_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1506_ = v_m_1500_;
v_isShared_1507_ = v_isSharedCheck_1547_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_buckets_1504_);
lean_inc(v_size_1503_);
lean_dec(v_m_1500_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1547_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; uint64_t v___x_1509_; uint64_t v___x_1510_; uint64_t v___x_1511_; uint64_t v_fold_1512_; uint64_t v___x_1513_; uint64_t v___x_1514_; uint64_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; lean_object* v_bkt_1521_; uint8_t v___x_1522_; 
v___x_1508_ = lean_array_get_size(v_buckets_1504_);
v___x_1509_ = l_Lean_Expr_hash(v_a_1501_);
v___x_1510_ = 32ULL;
v___x_1511_ = lean_uint64_shift_right(v___x_1509_, v___x_1510_);
v_fold_1512_ = lean_uint64_xor(v___x_1509_, v___x_1511_);
v___x_1513_ = 16ULL;
v___x_1514_ = lean_uint64_shift_right(v_fold_1512_, v___x_1513_);
v___x_1515_ = lean_uint64_xor(v_fold_1512_, v___x_1514_);
v___x_1516_ = lean_uint64_to_usize(v___x_1515_);
v___x_1517_ = lean_usize_of_nat(v___x_1508_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_sub(v___x_1517_, v___x_1518_);
v___x_1520_ = lean_usize_land(v___x_1516_, v___x_1519_);
v_bkt_1521_ = lean_array_uget_borrowed(v_buckets_1504_, v___x_1520_);
v___x_1522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1501_, v_bkt_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v_size_x27_1524_; lean_object* v___x_1525_; lean_object* v_buckets_x27_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v_size_x27_1524_ = lean_nat_add(v_size_1503_, v___x_1523_);
lean_dec(v_size_1503_);
lean_inc(v_bkt_1521_);
v___x_1525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1501_);
lean_ctor_set(v___x_1525_, 1, v_b_1502_);
lean_ctor_set(v___x_1525_, 2, v_bkt_1521_);
v_buckets_x27_1526_ = lean_array_uset(v_buckets_1504_, v___x_1520_, v___x_1525_);
v___x_1527_ = lean_unsigned_to_nat(4u);
v___x_1528_ = lean_nat_mul(v_size_x27_1524_, v___x_1527_);
v___x_1529_ = lean_unsigned_to_nat(3u);
v___x_1530_ = lean_nat_div(v___x_1528_, v___x_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_array_get_size(v_buckets_x27_1526_);
v___x_1532_ = lean_nat_dec_le(v___x_1530_, v___x_1531_);
lean_dec(v___x_1530_);
if (v___x_1532_ == 0)
{
lean_object* v_val_1533_; lean_object* v___x_1535_; 
v_val_1533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_buckets_x27_1526_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v_val_1533_);
lean_ctor_set(v___x_1506_, 0, v_size_x27_1524_);
v___x_1535_ = v___x_1506_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_size_x27_1524_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_val_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v___x_1538_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v_buckets_x27_1526_);
lean_ctor_set(v___x_1506_, 0, v_size_x27_1524_);
v___x_1538_ = v___x_1506_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_size_x27_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_buckets_x27_1526_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v_buckets_x27_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_inc(v_bkt_1521_);
v___x_1540_ = lean_box(0);
v_buckets_x27_1541_ = lean_array_uset(v_buckets_1504_, v___x_1520_, v___x_1540_);
v___x_1542_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1501_, v_b_1502_, v_bkt_1521_);
v___x_1543_ = lean_array_uset(v_buckets_x27_1541_, v___x_1520_, v___x_1542_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1543_);
v___x_1545_ = v___x_1506_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_size_1503_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(lean_object* v_a_1548_, lean_object* v_b_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_dec(v_b_1549_);
lean_dec(v_a_1548_);
return v_x_1550_;
}
else
{
lean_object* v_key_1551_; lean_object* v_value_1552_; lean_object* v_tail_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1565_; 
v_key_1551_ = lean_ctor_get(v_x_1550_, 0);
v_value_1552_ = lean_ctor_get(v_x_1550_, 1);
v_tail_1553_ = lean_ctor_get(v_x_1550_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1555_ = v_x_1550_;
v_isShared_1556_ = v_isSharedCheck_1565_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_tail_1553_);
lean_inc(v_value_1552_);
lean_inc(v_key_1551_);
lean_dec(v_x_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1565_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_eq(v_key_1551_, v_a_1548_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1548_, v_b_1549_, v_tail_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 2, v___x_1558_);
v___x_1560_ = v___x_1555_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_key_1551_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_value_1552_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
else
{
lean_object* v___x_1563_; 
lean_dec(v_value_1552_);
lean_dec(v_key_1551_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v_b_1549_);
lean_ctor_set(v___x_1555_, 0, v_a_1548_);
v___x_1563_ = v___x_1555_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_b_1549_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_tail_1553_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(lean_object* v_a_1566_, lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
uint8_t v___x_1568_; 
v___x_1568_ = 0;
return v___x_1568_;
}
else
{
lean_object* v_key_1569_; lean_object* v_tail_1570_; uint8_t v___x_1571_; 
v_key_1569_ = lean_ctor_get(v_x_1567_, 0);
v_tail_1570_ = lean_ctor_get(v_x_1567_, 2);
v___x_1571_ = lean_nat_dec_eq(v_key_1569_, v_a_1566_);
if (v___x_1571_ == 0)
{
v_x_1567_ = v_tail_1570_;
goto _start;
}
else
{
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg___boxed(lean_object* v_a_1573_, lean_object* v_x_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1573_, v_x_1574_);
lean_dec(v_x_1574_);
lean_dec(v_a_1573_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
if (lean_obj_tag(v_x_1578_) == 0)
{
return v_x_1577_;
}
else
{
lean_object* v_key_1579_; lean_object* v_value_1580_; lean_object* v_tail_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1604_; 
v_key_1579_ = lean_ctor_get(v_x_1578_, 0);
v_value_1580_ = lean_ctor_get(v_x_1578_, 1);
v_tail_1581_ = lean_ctor_get(v_x_1578_, 2);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1578_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1583_ = v_x_1578_;
v_isShared_1584_ = v_isSharedCheck_1604_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_tail_1581_);
lean_inc(v_value_1580_);
lean_inc(v_key_1579_);
lean_dec(v_x_1578_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1604_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; uint64_t v___x_1588_; uint64_t v_fold_1589_; uint64_t v___x_1590_; uint64_t v___x_1591_; uint64_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1585_ = lean_array_get_size(v_x_1577_);
v___x_1586_ = lean_uint64_of_nat(v_key_1579_);
v___x_1587_ = 32ULL;
v___x_1588_ = lean_uint64_shift_right(v___x_1586_, v___x_1587_);
v_fold_1589_ = lean_uint64_xor(v___x_1586_, v___x_1588_);
v___x_1590_ = 16ULL;
v___x_1591_ = lean_uint64_shift_right(v_fold_1589_, v___x_1590_);
v___x_1592_ = lean_uint64_xor(v_fold_1589_, v___x_1591_);
v___x_1593_ = lean_uint64_to_usize(v___x_1592_);
v___x_1594_ = lean_usize_of_nat(v___x_1585_);
v___x_1595_ = ((size_t)1ULL);
v___x_1596_ = lean_usize_sub(v___x_1594_, v___x_1595_);
v___x_1597_ = lean_usize_land(v___x_1593_, v___x_1596_);
v___x_1598_ = lean_array_uget_borrowed(v_x_1577_, v___x_1597_);
lean_inc(v___x_1598_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 2, v___x_1598_);
v___x_1600_ = v___x_1583_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_key_1579_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_value_1580_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_array_uset(v_x_1577_, v___x_1597_, v___x_1600_);
v_x_1577_ = v___x_1601_;
v_x_1578_ = v_tail_1581_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(lean_object* v_i_1605_, lean_object* v_source_1606_, lean_object* v_target_1607_){
_start:
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = lean_array_get_size(v_source_1606_);
v___x_1609_ = lean_nat_dec_lt(v_i_1605_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v_source_1606_);
lean_dec(v_i_1605_);
return v_target_1607_;
}
else
{
lean_object* v_es_1610_; lean_object* v___x_1611_; lean_object* v_source_1612_; lean_object* v_target_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_es_1610_ = lean_array_fget(v_source_1606_, v_i_1605_);
v___x_1611_ = lean_box(0);
v_source_1612_ = lean_array_fset(v_source_1606_, v_i_1605_, v___x_1611_);
v_target_1613_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1607_, v_es_1610_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_i_1605_, v___x_1614_);
lean_dec(v_i_1605_);
v_i_1605_ = v___x_1615_;
v_source_1606_ = v_source_1612_;
v_target_1607_ = v_target_1613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(lean_object* v_data_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v_nbuckets_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1618_ = lean_array_get_size(v_data_1617_);
v___x_1619_ = lean_unsigned_to_nat(2u);
v_nbuckets_1620_ = lean_nat_mul(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_mk_array(v_nbuckets_1620_, v___x_1622_);
v___x_1624_ = lean_array_propagate_mark(v_data_1617_, v___x_1623_);
v___x_1625_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v___x_1621_, v_data_1617_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(lean_object* v_m_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_){
_start:
{
lean_object* v_size_1629_; lean_object* v_buckets_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1673_; 
v_size_1629_ = lean_ctor_get(v_m_1626_, 0);
v_buckets_1630_ = lean_ctor_get(v_m_1626_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_m_1626_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1632_ = v_m_1626_;
v_isShared_1633_ = v_isSharedCheck_1673_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_buckets_1630_);
lean_inc(v_size_1629_);
lean_dec(v_m_1626_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1673_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; uint64_t v___x_1635_; uint64_t v___x_1636_; uint64_t v___x_1637_; uint64_t v_fold_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; lean_object* v_bkt_1647_; uint8_t v___x_1648_; 
v___x_1634_ = lean_array_get_size(v_buckets_1630_);
v___x_1635_ = lean_uint64_of_nat(v_a_1627_);
v___x_1636_ = 32ULL;
v___x_1637_ = lean_uint64_shift_right(v___x_1635_, v___x_1636_);
v_fold_1638_ = lean_uint64_xor(v___x_1635_, v___x_1637_);
v___x_1639_ = 16ULL;
v___x_1640_ = lean_uint64_shift_right(v_fold_1638_, v___x_1639_);
v___x_1641_ = lean_uint64_xor(v_fold_1638_, v___x_1640_);
v___x_1642_ = lean_uint64_to_usize(v___x_1641_);
v___x_1643_ = lean_usize_of_nat(v___x_1634_);
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_sub(v___x_1643_, v___x_1644_);
v___x_1646_ = lean_usize_land(v___x_1642_, v___x_1645_);
v_bkt_1647_ = lean_array_uget_borrowed(v_buckets_1630_, v___x_1646_);
v___x_1648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1627_, v_bkt_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v_size_x27_1650_; lean_object* v___x_1651_; lean_object* v_buckets_x27_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1649_ = lean_unsigned_to_nat(1u);
v_size_x27_1650_ = lean_nat_add(v_size_1629_, v___x_1649_);
lean_dec(v_size_1629_);
lean_inc(v_bkt_1647_);
v___x_1651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1651_, 0, v_a_1627_);
lean_ctor_set(v___x_1651_, 1, v_b_1628_);
lean_ctor_set(v___x_1651_, 2, v_bkt_1647_);
v_buckets_x27_1652_ = lean_array_uset(v_buckets_1630_, v___x_1646_, v___x_1651_);
v___x_1653_ = lean_unsigned_to_nat(4u);
v___x_1654_ = lean_nat_mul(v_size_x27_1650_, v___x_1653_);
v___x_1655_ = lean_unsigned_to_nat(3u);
v___x_1656_ = lean_nat_div(v___x_1654_, v___x_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_array_get_size(v_buckets_x27_1652_);
v___x_1658_ = lean_nat_dec_le(v___x_1656_, v___x_1657_);
lean_dec(v___x_1656_);
if (v___x_1658_ == 0)
{
lean_object* v_val_1659_; lean_object* v___x_1661_; 
v_val_1659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_buckets_x27_1652_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_val_1659_);
lean_ctor_set(v___x_1632_, 0, v_size_x27_1650_);
v___x_1661_ = v___x_1632_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_size_x27_1650_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_val_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
else
{
lean_object* v___x_1664_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_buckets_x27_1652_);
lean_ctor_set(v___x_1632_, 0, v_size_x27_1650_);
v___x_1664_ = v___x_1632_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_size_x27_1650_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_buckets_x27_1652_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v_buckets_x27_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_inc(v_bkt_1647_);
v___x_1666_ = lean_box(0);
v_buckets_x27_1667_ = lean_array_uset(v_buckets_1630_, v___x_1646_, v___x_1666_);
v___x_1668_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1627_, v_b_1628_, v_bkt_1647_);
v___x_1669_ = lean_array_uset(v_buckets_x27_1667_, v___x_1646_, v___x_1668_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v___x_1669_);
v___x_1671_ = v___x_1632_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_size_1629_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2));
v___x_1678_ = lean_unsigned_to_nat(48u);
v___x_1679_ = lean_unsigned_to_nat(239u);
v___x_1680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1));
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0));
v___x_1682_ = l_mkPanicMessageWithDecl(v___x_1681_, v___x_1680_, v___x_1679_, v___x_1678_, v___x_1677_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(lean_object* v_as_1683_, size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_b_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_a_1700_; uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_b_1686_);
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v_snd_1707_; lean_object* v_fst_1708_; lean_object* v_snd_1709_; lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1744_; 
v_a_1706_ = lean_array_uget_borrowed(v_as_1683_, v_i_1685_);
v_snd_1707_ = lean_ctor_get(v_a_1706_, 1);
v_fst_1708_ = lean_ctor_get(v_a_1706_, 0);
v_snd_1709_ = lean_ctor_get(v_snd_1707_, 1);
v_fst_1710_ = lean_ctor_get(v_b_1686_, 0);
v_snd_1711_ = lean_ctor_get(v_b_1686_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_b_1686_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1713_ = v_b_1686_;
v_isShared_1714_ = v_isSharedCheck_1744_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_snd_1711_);
lean_inc(v_fst_1710_);
lean_dec(v_b_1686_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1744_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_fst_1708_, v___y_1688_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
if (lean_obj_tag(v_a_1716_) == 1)
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v_val_1717_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v_a_1716_, 1);
lean_inc_n(v_snd_1709_, 2);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_snd_1711_, v_val_1717_, v_snd_1709_);
lean_inc(v_fst_1708_);
v___x_1719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_fst_1710_, v_fst_1708_, v_snd_1709_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1718_);
lean_ctor_set(v___x_1713_, 0, v___x_1719_);
v___x_1721_ = v___x_1713_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1718_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
v_a_1700_ = v___x_1721_;
goto v___jp_1699_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_a_1716_);
v___x_1723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3);
v___x_1724_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v___x_1723_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1726_; 
lean_dec_ref_known(v___x_1724_, 1);
if (v_isShared_1714_ == 0)
{
v___x_1726_ = v___x_1713_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_fst_1710_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1711_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
v_a_1700_ = v___x_1726_;
goto v___jp_1699_;
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1713_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
v_a_1728_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1724_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1724_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_del_object(v___x_1713_);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
v_a_1736_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1715_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1715_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
v___jp_1699_:
{
size_t v___x_1701_; size_t v___x_1702_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1685_, v___x_1701_);
v_i_1685_ = v___x_1702_;
v_b_1686_ = v_a_1700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___boxed(lean_object* v_as_1745_, lean_object* v_sz_1746_, lean_object* v_i_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_sz_boxed_1761_; size_t v_i_boxed_1762_; lean_object* v_res_1763_; 
v_sz_boxed_1761_ = lean_unbox_usize(v_sz_1746_);
lean_dec(v_sz_1746_);
v_i_boxed_1762_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_as_1745_, v_sz_boxed_1761_, v_i_boxed_1762_, v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_as_1745_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object* v_arr_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_exprCex_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_atomCex_1787_; lean_object* v___x_1788_; size_t v_sz_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_box(0);
v_exprCex_1779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_1780_ = lean_array_get_size(v_arr_1764_);
v___x_1781_ = lean_unsigned_to_nat(4u);
v___x_1782_ = lean_nat_mul(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_unsigned_to_nat(3u);
v___x_1784_ = lean_nat_div(v___x_1782_, v___x_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = l_Nat_nextPowerOfTwo(v___x_1784_);
lean_dec(v___x_1784_);
v___x_1786_ = lean_mk_array(v___x_1785_, v___x_1778_);
v_atomCex_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_atomCex_1787_, 0, v___x_1777_);
lean_ctor_set(v_atomCex_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_exprCex_1779_);
lean_ctor_set(v___x_1788_, 1, v_atomCex_1787_);
v_sz_1789_ = lean_array_size(v_arr_1764_);
v___x_1790_ = ((size_t)0ULL);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_arr_1764_, v_sz_1789_, v___x_1790_, v___x_1788_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1808_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_fst_1796_; lean_object* v_snd_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1807_; 
v_fst_1796_ = lean_ctor_get(v_a_1792_, 0);
v_snd_1797_ = lean_ctor_get(v_a_1792_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_a_1792_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1799_ = v_a_1792_;
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snd_1797_);
lean_inc(v_fst_1796_);
lean_dec(v_a_1792_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_fst_1796_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_snd_1797_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1802_);
v___x_1804_ = v___x_1794_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1791_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1791_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object* v_arr_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_arr_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec_ref(v_arr_1817_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0(lean_object* v_00_u03b2_1831_, lean_object* v_m_1832_, lean_object* v_a_1833_, lean_object* v_b_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_m_1832_, v_a_1833_, v_b_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1(lean_object* v_00_u03b2_1836_, lean_object* v_m_1837_, lean_object* v_a_1838_, lean_object* v_b_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_m_1837_, v_a_1838_, v_b_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_object* v_00_u03b2_1841_, lean_object* v_a_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_a_1846_, lean_object* v_x_1847_){
_start:
{
uint8_t v_res_1848_; lean_object* v_r_1849_; 
v_res_1848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(v_00_u03b2_1845_, v_a_1846_, v_x_1847_);
lean_dec(v_x_1847_);
lean_dec(v_a_1846_);
v_r_1849_ = lean_box(v_res_1848_);
return v_r_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1(lean_object* v_00_u03b2_1850_, lean_object* v_data_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_data_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2(lean_object* v_00_u03b2_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1854_, v_b_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_object* v_00_u03b2_1858_, lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1859_, v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1862_, lean_object* v_a_1863_, lean_object* v_x_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(v_00_u03b2_1862_, v_a_1863_, v_x_1864_);
lean_dec(v_x_1864_);
lean_dec_ref(v_a_1863_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5(lean_object* v_00_u03b2_1867_, lean_object* v_data_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_data_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6(lean_object* v_00_u03b2_1870_, lean_object* v_a_1871_, lean_object* v_b_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1871_, v_b_1872_, v_x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1875_, lean_object* v_i_1876_, lean_object* v_source_1877_, lean_object* v_target_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v_i_1876_, v_source_1877_, v_target_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8(lean_object* v_00_u03b2_1880_, lean_object* v_i_1881_, lean_object* v_source_1882_, lean_object* v_target_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v_i_1881_, v_source_1882_, v_target_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object* v_cert_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_cert_1897_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object* v_cert_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_usedHyps_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = lean_st_ref_get(v_a_1902_);
v_usedHyps_1905_ = lean_ctor_get(v___x_1904_, 2);
lean_inc_ref(v_usedHyps_1905_);
lean_dec(v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_usedHyps_1905_);
lean_ctor_set(v___x_1906_, 1, v_cert_1901_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg___boxed(lean_object* v_cert_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1908_, v_a_1909_);
lean_dec(v_a_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(lean_object* v_cert_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1912_, v_a_1914_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___boxed(lean_object* v_cert_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(v_cert_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1945_;
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
