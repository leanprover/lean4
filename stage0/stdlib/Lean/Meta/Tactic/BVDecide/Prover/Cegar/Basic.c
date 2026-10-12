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
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
return v_res_56_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_satExpr_61_; lean_object* v_unusedHypotheses_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_60_ = lean_st_ref_get(v_a_58_);
v_satExpr_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_satExpr_61_);
lean_dec(v___x_60_);
v_unusedHypotheses_62_ = lean_ctor_get(v_a_57_, 1);
lean_inc_ref(v_unusedHypotheses_62_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v_satExpr_61_);
lean_ctor_set(v___x_63_, 1, v_unusedHypotheses_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_57_, v_a_58_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg___boxed(lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_69_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v_a_70_, v_a_71_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_70_ = stack[0].m_obj;
lean_object* v_a_71_ = stack[1].m_obj;
lean_object* v_a_72_ = stack[2].m_obj;
lean_object* v_a_73_ = stack[3].m_obj;
lean_object* v_a_74_ = stack[4].m_obj;
lean_object* v_a_75_ = stack[5].m_obj;
lean_object* v_a_76_ = stack[6].m_obj;
lean_object* v_a_77_ = stack[7].m_obj;
lean_object* v_a_78_ = stack[8].m_obj;
lean_object* v_a_79_ = stack[9].m_obj;
lean_object* v_a_80_ = stack[10].m_obj;
lean_object* v_a_81_ = stack[11].m_obj;
lean_object* v_a_82_ = stack[12].m_obj;
lean_object* v_a_83_ = stack[13].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___boxed(lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult(v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_102_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; uint8_t v_didChange_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_st_ref_get(v_a_103_);
v_didChange_106_ = lean_ctor_get_uint8(v___x_105_, sizeof(void*)*6);
lean_dec(v___x_105_);
v___x_107_ = lean_box(v_didChange_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_103_ = stack[0].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(v_a_103_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg___boxed(lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___redArg(v_a_110_);
lean_dec(v_a_110_);
return v_res_112_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; uint8_t v_didChange_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_st_ref_get(v_a_114_);
v_didChange_129_ = lean_ctor_get_uint8(v___x_128_, sizeof(void*)*6);
lean_dec(v___x_128_);
v___x_130_ = lean_box(v_didChange_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_113_ = stack[0].m_obj;
lean_object* v_a_114_ = stack[1].m_obj;
lean_object* v_a_115_ = stack[2].m_obj;
lean_object* v_a_116_ = stack[3].m_obj;
lean_object* v_a_117_ = stack[4].m_obj;
lean_object* v_a_118_ = stack[5].m_obj;
lean_object* v_a_119_ = stack[6].m_obj;
lean_object* v_a_120_ = stack[7].m_obj;
lean_object* v_a_121_ = stack[8].m_obj;
lean_object* v_a_122_ = stack[9].m_obj;
lean_object* v_a_123_ = stack[10].m_obj;
lean_object* v_a_124_ = stack[11].m_obj;
lean_object* v_a_125_ = stack[12].m_obj;
lean_object* v_a_126_ = stack[13].m_obj;
lean_object* v_res_132_;
v_res_132_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
stack->m_obj
 = v_res_132_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange___boxed(lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getDidChange(v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_148_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(uint8_t v_v_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; lean_object* v_satExpr_153_; lean_object* v_hypQueue_154_; lean_object* v_usedHyps_155_; lean_object* v_theoryState_156_; lean_object* v_solverTimeBudgetMs_157_; lean_object* v_roundBudget_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
v___x_152_ = lean_st_ref_take(v_a_150_);
v_satExpr_153_ = lean_ctor_get(v___x_152_, 0);
v_hypQueue_154_ = lean_ctor_get(v___x_152_, 1);
v_usedHyps_155_ = lean_ctor_get(v___x_152_, 2);
v_theoryState_156_ = lean_ctor_get(v___x_152_, 3);
v_solverTimeBudgetMs_157_ = lean_ctor_get(v___x_152_, 4);
v_roundBudget_158_ = lean_ctor_get(v___x_152_, 5);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_168_ == 0)
{
v___x_160_ = v___x_152_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_roundBudget_158_);
lean_inc(v_solverTimeBudgetMs_157_);
lean_inc(v_theoryState_156_);
lean_inc(v_usedHyps_155_);
lean_inc(v_hypQueue_154_);
lean_inc(v_satExpr_153_);
lean_dec(v___x_152_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
if (v_isShared_161_ == 0)
{
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_satExpr_153_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_hypQueue_154_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_usedHyps_155_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_theoryState_156_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_solverTimeBudgetMs_157_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_roundBudget_158_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*6, v_v_149_);
v___x_165_ = lean_st_ref_put(v_a_150_, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_162_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_149_ = stack[0].m_num;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(v_v_149_, v_a_150_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg___boxed(lean_object* v_v_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
uint8_t v_v_boxed_173_; lean_object* v_res_174_; 
v_v_boxed_173_ = lean_unbox(v_v_170_);
v_res_174_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___redArg(v_v_boxed_173_, v_a_171_);
lean_dec(v_a_171_);
return v_res_174_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(uint8_t v_v_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; lean_object* v_satExpr_192_; lean_object* v_hypQueue_193_; lean_object* v_usedHyps_194_; lean_object* v_theoryState_195_; lean_object* v_solverTimeBudgetMs_196_; lean_object* v_roundBudget_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_207_; 
v___x_191_ = lean_st_ref_take(v_a_177_);
v_satExpr_192_ = lean_ctor_get(v___x_191_, 0);
v_hypQueue_193_ = lean_ctor_get(v___x_191_, 1);
v_usedHyps_194_ = lean_ctor_get(v___x_191_, 2);
v_theoryState_195_ = lean_ctor_get(v___x_191_, 3);
v_solverTimeBudgetMs_196_ = lean_ctor_get(v___x_191_, 4);
v_roundBudget_197_ = lean_ctor_get(v___x_191_, 5);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_207_ == 0)
{
v___x_199_ = v___x_191_;
v_isShared_200_ = v_isSharedCheck_207_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_roundBudget_197_);
lean_inc(v_solverTimeBudgetMs_196_);
lean_inc(v_theoryState_195_);
lean_inc(v_usedHyps_194_);
lean_inc(v_hypQueue_193_);
lean_inc(v_satExpr_192_);
lean_dec(v___x_191_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_207_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_box(0);
if (v_isShared_200_ == 0)
{
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_satExpr_192_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_hypQueue_193_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_usedHyps_194_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_theoryState_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_solverTimeBudgetMs_196_);
lean_ctor_set(v_reuseFailAlloc_206_, 5, v_roundBudget_197_);
v___x_203_ = v_reuseFailAlloc_206_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*6, v_v_175_);
v___x_204_ = lean_st_ref_put(v_a_177_, v___x_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_201_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange_0interp(lean_interpreter_value* stack)
{
uint8_t v_v_175_ = stack[0].m_num;
lean_object* v_a_176_ = stack[1].m_obj;
lean_object* v_a_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_a_180_ = stack[5].m_obj;
lean_object* v_a_181_ = stack[6].m_obj;
lean_object* v_a_182_ = stack[7].m_obj;
lean_object* v_a_183_ = stack[8].m_obj;
lean_object* v_a_184_ = stack[9].m_obj;
lean_object* v_a_185_ = stack[10].m_obj;
lean_object* v_a_186_ = stack[11].m_obj;
lean_object* v_a_187_ = stack[12].m_obj;
lean_object* v_a_188_ = stack[13].m_obj;
lean_object* v_a_189_ = stack[14].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(v_v_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange___boxed(lean_object* v_v_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
uint8_t v_v_boxed_225_; lean_object* v_res_226_; 
v_v_boxed_225_ = lean_unbox(v_v_209_);
v_res_226_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setDidChange(v_v_boxed_225_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_226_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_theoryState_230_; lean_object* v___x_231_; 
v___x_229_ = lean_st_ref_get(v_a_227_);
v_theoryState_230_ = lean_ctor_get(v___x_229_, 3);
lean_inc_ref(v_theoryState_230_);
lean_dec(v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_theoryState_230_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_227_ = stack[0].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(v_a_227_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg___boxed(lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___redArg(v_a_233_);
lean_dec(v_a_233_);
return v_res_235_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_theoryState_252_; lean_object* v___x_253_; 
v___x_251_ = lean_st_ref_get(v_a_237_);
v_theoryState_252_ = lean_ctor_get(v___x_251_, 3);
lean_inc_ref(v_theoryState_252_);
lean_dec(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_theoryState_252_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_236_ = stack[0].m_obj;
lean_object* v_a_237_ = stack[1].m_obj;
lean_object* v_a_238_ = stack[2].m_obj;
lean_object* v_a_239_ = stack[3].m_obj;
lean_object* v_a_240_ = stack[4].m_obj;
lean_object* v_a_241_ = stack[5].m_obj;
lean_object* v_a_242_ = stack[6].m_obj;
lean_object* v_a_243_ = stack[7].m_obj;
lean_object* v_a_244_ = stack[8].m_obj;
lean_object* v_a_245_ = stack[9].m_obj;
lean_object* v_a_246_ = stack[10].m_obj;
lean_object* v_a_247_ = stack[11].m_obj;
lean_object* v_a_248_ = stack[12].m_obj;
lean_object* v_a_249_ = stack[13].m_obj;
lean_object* v_res_254_;
v_res_254_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState___boxed(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTheoryState(v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_270_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(lean_object* v_f_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_satExpr_275_; lean_object* v_hypQueue_276_; lean_object* v_usedHyps_277_; uint8_t v_didChange_278_; lean_object* v_theoryState_279_; lean_object* v_solverTimeBudgetMs_280_; lean_object* v_roundBudget_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_292_; 
v___x_274_ = lean_st_ref_take(v_a_272_);
v_satExpr_275_ = lean_ctor_get(v___x_274_, 0);
v_hypQueue_276_ = lean_ctor_get(v___x_274_, 1);
v_usedHyps_277_ = lean_ctor_get(v___x_274_, 2);
v_didChange_278_ = lean_ctor_get_uint8(v___x_274_, sizeof(void*)*6);
v_theoryState_279_ = lean_ctor_get(v___x_274_, 3);
v_solverTimeBudgetMs_280_ = lean_ctor_get(v___x_274_, 4);
v_roundBudget_281_ = lean_ctor_get(v___x_274_, 5);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_292_ == 0)
{
v___x_283_ = v___x_274_;
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_roundBudget_281_);
lean_inc(v_solverTimeBudgetMs_280_);
lean_inc(v_theoryState_279_);
lean_inc(v_usedHyps_277_);
lean_inc(v_hypQueue_276_);
lean_inc(v_satExpr_275_);
lean_dec(v___x_274_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_1(v_f_271_, v_theoryState_279_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 3, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_satExpr_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_hypQueue_276_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_usedHyps_277_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_solverTimeBudgetMs_280_);
lean_ctor_set(v_reuseFailAlloc_291_, 5, v_roundBudget_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*6, v_didChange_278_);
v___x_288_ = v_reuseFailAlloc_291_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_st_ref_put(v_a_272_, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_285_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_271_ = stack[0].m_obj;
lean_object* v_a_272_ = stack[1].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(v_f_271_, v_a_272_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg___boxed(lean_object* v_f_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___redArg(v_f_294_, v_a_295_);
lean_dec(v_a_295_);
return v_res_297_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; lean_object* v_satExpr_315_; lean_object* v_hypQueue_316_; lean_object* v_usedHyps_317_; uint8_t v_didChange_318_; lean_object* v_theoryState_319_; lean_object* v_solverTimeBudgetMs_320_; lean_object* v_roundBudget_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
v___x_314_ = lean_st_ref_take(v_a_300_);
v_satExpr_315_ = lean_ctor_get(v___x_314_, 0);
v_hypQueue_316_ = lean_ctor_get(v___x_314_, 1);
v_usedHyps_317_ = lean_ctor_get(v___x_314_, 2);
v_didChange_318_ = lean_ctor_get_uint8(v___x_314_, sizeof(void*)*6);
v_theoryState_319_ = lean_ctor_get(v___x_314_, 3);
v_solverTimeBudgetMs_320_ = lean_ctor_get(v___x_314_, 4);
v_roundBudget_321_ = lean_ctor_get(v___x_314_, 5);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_332_ == 0)
{
v___x_323_ = v___x_314_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_roundBudget_321_);
lean_inc(v_solverTimeBudgetMs_320_);
lean_inc(v_theoryState_319_);
lean_inc(v_usedHyps_317_);
lean_inc(v_hypQueue_316_);
lean_inc(v_satExpr_315_);
lean_dec(v___x_314_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_box(0);
v___x_326_ = lean_apply_1(v_f_298_, v_theoryState_319_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_satExpr_315_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_hypQueue_316_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_usedHyps_317_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_solverTimeBudgetMs_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 5, v_roundBudget_321_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*6, v_didChange_318_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_st_ref_put(v_a_300_, v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_325_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_298_ = stack[0].m_obj;
lean_object* v_a_299_ = stack[1].m_obj;
lean_object* v_a_300_ = stack[2].m_obj;
lean_object* v_a_301_ = stack[3].m_obj;
lean_object* v_a_302_ = stack[4].m_obj;
lean_object* v_a_303_ = stack[5].m_obj;
lean_object* v_a_304_ = stack[6].m_obj;
lean_object* v_a_305_ = stack[7].m_obj;
lean_object* v_a_306_ = stack[8].m_obj;
lean_object* v_a_307_ = stack[9].m_obj;
lean_object* v_a_308_ = stack[10].m_obj;
lean_object* v_a_309_ = stack[11].m_obj;
lean_object* v_a_310_ = stack[12].m_obj;
lean_object* v_a_311_ = stack[13].m_obj;
lean_object* v_a_312_ = stack[14].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(v_f_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState___boxed(lean_object* v_f_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Meta_Tactic_BVDecide_CegarM_modifyTheoryState(v_f_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_350_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Sat_AIG_empty___redArg();
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_353_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__1);
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_356_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__0);
v___x_357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_354_);
return v___x_357_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_satExpr_361_; lean_object* v_hypQueue_362_; lean_object* v_usedHyps_363_; uint8_t v_didChange_364_; lean_object* v_theoryState_365_; lean_object* v_solverTimeBudgetMs_366_; lean_object* v_roundBudget_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_391_; 
v___x_360_ = lean_st_ref_take(v_a_358_);
v_satExpr_361_ = lean_ctor_get(v___x_360_, 0);
v_hypQueue_362_ = lean_ctor_get(v___x_360_, 1);
v_usedHyps_363_ = lean_ctor_get(v___x_360_, 2);
v_didChange_364_ = lean_ctor_get_uint8(v___x_360_, sizeof(void*)*6);
v_theoryState_365_ = lean_ctor_get(v___x_360_, 3);
v_solverTimeBudgetMs_366_ = lean_ctor_get(v___x_360_, 4);
v_roundBudget_367_ = lean_ctor_get(v___x_360_, 5);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_391_ == 0)
{
v___x_369_ = v___x_360_;
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_roundBudget_367_);
lean_inc(v_solverTimeBudgetMs_366_);
lean_inc(v_theoryState_365_);
lean_inc(v_usedHyps_363_);
lean_inc(v_hypQueue_362_);
lean_inc(v_satExpr_361_);
lean_dec(v___x_360_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v_satSolver_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_387_; 
v___x_371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_372_ = lean_ctor_get(v_theoryState_365_, 3);
v_isSharedCheck_387_ = !lean_is_exclusive(v_theoryState_365_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_388_ = lean_ctor_get(v_theoryState_365_, 2);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_theoryState_365_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_theoryState_365_, 0);
lean_dec(v_unused_390_);
v___x_374_ = v_theoryState_365_;
v_isShared_375_ = v_isSharedCheck_387_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_satSolver_372_);
lean_dec(v_theoryState_365_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_387_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_377_ = lean_box(0);
v___x_378_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 2, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_378_);
lean_ctor_set(v___x_374_, 0, v___x_376_);
v___x_380_ = v___x_374_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_satSolver_372_);
v___x_380_ = v_reuseFailAlloc_386_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 3, v___x_380_);
v___x_382_ = v___x_369_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_satExpr_361_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_hypQueue_362_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_usedHyps_363_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_solverTimeBudgetMs_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 5, v_roundBudget_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_385_, sizeof(void*)*6, v_didChange_364_);
v___x_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_st_ref_put(v_a_358_, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_377_);
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_358_ = stack[0].m_obj;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(v_a_358_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___boxed(lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg(v_a_393_);
lean_dec(v_a_393_);
return v_res_395_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_satExpr_412_; lean_object* v_hypQueue_413_; lean_object* v_usedHyps_414_; uint8_t v_didChange_415_; lean_object* v_theoryState_416_; lean_object* v_solverTimeBudgetMs_417_; lean_object* v_roundBudget_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_442_; 
v___x_411_ = lean_st_ref_take(v_a_397_);
v_satExpr_412_ = lean_ctor_get(v___x_411_, 0);
v_hypQueue_413_ = lean_ctor_get(v___x_411_, 1);
v_usedHyps_414_ = lean_ctor_get(v___x_411_, 2);
v_didChange_415_ = lean_ctor_get_uint8(v___x_411_, sizeof(void*)*6);
v_theoryState_416_ = lean_ctor_get(v___x_411_, 3);
v_solverTimeBudgetMs_417_ = lean_ctor_get(v___x_411_, 4);
v_roundBudget_418_ = lean_ctor_get(v___x_411_, 5);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_442_ == 0)
{
v___x_420_ = v___x_411_;
v_isShared_421_ = v_isSharedCheck_442_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_roundBudget_418_);
lean_inc(v_solverTimeBudgetMs_417_);
lean_inc(v_theoryState_416_);
lean_inc(v_usedHyps_414_);
lean_inc(v_hypQueue_413_);
lean_inc(v_satExpr_412_);
lean_dec(v___x_411_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_442_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v_satSolver_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_438_; 
v___x_422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
v_satSolver_423_ = lean_ctor_get(v_theoryState_416_, 3);
v_isSharedCheck_438_ = !lean_is_exclusive(v_theoryState_416_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; lean_object* v_unused_441_; 
v_unused_439_ = lean_ctor_get(v_theoryState_416_, 2);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_theoryState_416_, 1);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_theoryState_416_, 0);
lean_dec(v_unused_441_);
v___x_425_ = v_theoryState_416_;
v_isShared_426_ = v_isSharedCheck_438_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_satSolver_423_);
lean_dec(v_theoryState_416_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_438_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_428_ = lean_box(0);
v___x_429_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___redArg___closed__2);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 2, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_429_);
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_satSolver_423_);
v___x_431_ = v_reuseFailAlloc_437_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 3, v___x_431_);
v___x_433_ = v___x_420_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_satExpr_412_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_hypQueue_413_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_usedHyps_414_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_solverTimeBudgetMs_417_);
lean_ctor_set(v_reuseFailAlloc_436_, 5, v_roundBudget_418_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*6, v_didChange_415_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_st_ref_put(v_a_397_, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_428_);
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_396_ = stack[0].m_obj;
lean_object* v_a_397_ = stack[1].m_obj;
lean_object* v_a_398_ = stack[2].m_obj;
lean_object* v_a_399_ = stack[3].m_obj;
lean_object* v_a_400_ = stack[4].m_obj;
lean_object* v_a_401_ = stack[5].m_obj;
lean_object* v_a_402_ = stack[6].m_obj;
lean_object* v_a_403_ = stack[7].m_obj;
lean_object* v_a_404_ = stack[8].m_obj;
lean_object* v_a_405_ = stack[9].m_obj;
lean_object* v_a_406_ = stack[10].m_obj;
lean_object* v_a_407_ = stack[11].m_obj;
lean_object* v_a_408_ = stack[12].m_obj;
lean_object* v_a_409_ = stack[13].m_obj;
lean_object* v_res_443_;
v_res_443_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches___boxed(lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_Tactic_BVDecide_CegarM_clearCaches(v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
return v_res_459_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(lean_object* v_hyp_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; lean_object* v_satExpr_464_; lean_object* v_hypQueue_465_; lean_object* v_usedHyps_466_; uint8_t v_didChange_467_; lean_object* v_theoryState_468_; lean_object* v_solverTimeBudgetMs_469_; lean_object* v_roundBudget_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_481_; 
v___x_463_ = lean_st_ref_take(v_a_461_);
v_satExpr_464_ = lean_ctor_get(v___x_463_, 0);
v_hypQueue_465_ = lean_ctor_get(v___x_463_, 1);
v_usedHyps_466_ = lean_ctor_get(v___x_463_, 2);
v_didChange_467_ = lean_ctor_get_uint8(v___x_463_, sizeof(void*)*6);
v_theoryState_468_ = lean_ctor_get(v___x_463_, 3);
v_solverTimeBudgetMs_469_ = lean_ctor_get(v___x_463_, 4);
v_roundBudget_470_ = lean_ctor_get(v___x_463_, 5);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_481_ == 0)
{
v___x_472_ = v___x_463_;
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_roundBudget_470_);
lean_inc(v_solverTimeBudgetMs_469_);
lean_inc(v_theoryState_468_);
lean_inc(v_usedHyps_466_);
lean_inc(v_hypQueue_465_);
lean_inc(v_satExpr_464_);
lean_dec(v___x_463_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_array_push(v_hypQueue_465_, v_hyp_460_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_satExpr_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_usedHyps_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_theoryState_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_solverTimeBudgetMs_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_roundBudget_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*6, v_didChange_467_);
v___x_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_st_ref_put(v_a_461_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_474_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_460_ = stack[0].m_obj;
lean_object* v_a_461_ = stack[1].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___redArg(v_hyp_460_, v_a_461_);
stack->m_obj
 = v_res_482_;
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
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(lean_object* v_hyp_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_487_ = stack[0].m_obj;
lean_object* v_a_488_ = stack[1].m_obj;
lean_object* v_a_489_ = stack[2].m_obj;
lean_object* v_a_490_ = stack[3].m_obj;
lean_object* v_a_491_ = stack[4].m_obj;
lean_object* v_a_492_ = stack[5].m_obj;
lean_object* v_a_493_ = stack[6].m_obj;
lean_object* v_a_494_ = stack[7].m_obj;
lean_object* v_a_495_ = stack[8].m_obj;
lean_object* v_a_496_ = stack[9].m_obj;
lean_object* v_a_497_ = stack[10].m_obj;
lean_object* v_a_498_ = stack[11].m_obj;
lean_object* v_a_499_ = stack[12].m_obj;
lean_object* v_a_500_ = stack[13].m_obj;
lean_object* v_a_501_ = stack[14].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(v_hyp_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp___boxed(lean_object* v_hyp_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Meta_Tactic_BVDecide_CegarM_pushNewHyp(v_hyp_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
return v_res_539_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v_usedHyps_543_; lean_object* v___x_544_; 
v___x_542_ = lean_st_ref_get(v_a_540_);
v_usedHyps_543_ = lean_ctor_get(v___x_542_, 2);
lean_inc_ref(v_usedHyps_543_);
lean_dec(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_usedHyps_543_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_540_ = stack[0].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(v_a_540_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg___boxed(lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___redArg(v_a_546_);
lean_dec(v_a_546_);
return v_res_548_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_usedHyps_565_; lean_object* v___x_566_; 
v___x_564_ = lean_st_ref_get(v_a_550_);
v_usedHyps_565_ = lean_ctor_get(v___x_564_, 2);
lean_inc_ref(v_usedHyps_565_);
lean_dec(v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_usedHyps_565_);
return v___x_566_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_549_ = stack[0].m_obj;
lean_object* v_a_550_ = stack[1].m_obj;
lean_object* v_a_551_ = stack[2].m_obj;
lean_object* v_a_552_ = stack[3].m_obj;
lean_object* v_a_553_ = stack[4].m_obj;
lean_object* v_a_554_ = stack[5].m_obj;
lean_object* v_a_555_ = stack[6].m_obj;
lean_object* v_a_556_ = stack[7].m_obj;
lean_object* v_a_557_ = stack[8].m_obj;
lean_object* v_a_558_ = stack[9].m_obj;
lean_object* v_a_559_ = stack[10].m_obj;
lean_object* v_a_560_ = stack[11].m_obj;
lean_object* v_a_561_ = stack[12].m_obj;
lean_object* v_a_562_ = stack[13].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps___boxed(lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getUsedHyps(v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
return v_res_583_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; lean_object* v_satExpr_589_; lean_object* v_hypQueue_590_; lean_object* v_usedHyps_591_; uint8_t v_didChange_592_; lean_object* v_theoryState_593_; lean_object* v_solverTimeBudgetMs_594_; lean_object* v_roundBudget_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_606_; 
v___x_588_ = lean_st_ref_take(v_a_586_);
v_satExpr_589_ = lean_ctor_get(v___x_588_, 0);
v_hypQueue_590_ = lean_ctor_get(v___x_588_, 1);
v_usedHyps_591_ = lean_ctor_get(v___x_588_, 2);
v_didChange_592_ = lean_ctor_get_uint8(v___x_588_, sizeof(void*)*6);
v_theoryState_593_ = lean_ctor_get(v___x_588_, 3);
v_solverTimeBudgetMs_594_ = lean_ctor_get(v___x_588_, 4);
v_roundBudget_595_ = lean_ctor_get(v___x_588_, 5);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_606_ == 0)
{
v___x_597_ = v___x_588_;
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_roundBudget_595_);
lean_inc(v_solverTimeBudgetMs_594_);
lean_inc(v_theoryState_593_);
lean_inc(v_usedHyps_591_);
lean_inc(v_hypQueue_590_);
lean_inc(v_satExpr_589_);
lean_dec(v___x_588_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_600_ = l_Array_append___redArg(v_usedHyps_591_, v_hypQueue_590_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v___x_600_);
lean_ctor_set(v___x_597_, 1, v___x_599_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_satExpr_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_theoryState_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_solverTimeBudgetMs_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v_roundBudget_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*6, v_didChange_592_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_st_ref_put(v_a_586_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_hypQueue_590_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_586_ = stack[0].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(v_a_586_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___boxed(lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg(v_a_608_);
lean_dec(v_a_608_);
return v_res_610_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v___x_626_; lean_object* v_satExpr_627_; lean_object* v_hypQueue_628_; lean_object* v_usedHyps_629_; uint8_t v_didChange_630_; lean_object* v_theoryState_631_; lean_object* v_solverTimeBudgetMs_632_; lean_object* v_roundBudget_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_644_; 
v___x_626_ = lean_st_ref_take(v_a_612_);
v_satExpr_627_ = lean_ctor_get(v___x_626_, 0);
v_hypQueue_628_ = lean_ctor_get(v___x_626_, 1);
v_usedHyps_629_ = lean_ctor_get(v___x_626_, 2);
v_didChange_630_ = lean_ctor_get_uint8(v___x_626_, sizeof(void*)*6);
v_theoryState_631_ = lean_ctor_get(v___x_626_, 3);
v_solverTimeBudgetMs_632_ = lean_ctor_get(v___x_626_, 4);
v_roundBudget_633_ = lean_ctor_get(v___x_626_, 5);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_644_ == 0)
{
v___x_635_ = v___x_626_;
v_isShared_636_ = v_isSharedCheck_644_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_roundBudget_633_);
lean_inc(v_solverTimeBudgetMs_632_);
lean_inc(v_theoryState_631_);
lean_inc(v_usedHyps_629_);
lean_inc(v_hypQueue_628_);
lean_inc(v_satExpr_627_);
lean_dec(v___x_626_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_644_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_638_ = l_Array_append___redArg(v_usedHyps_629_, v_hypQueue_628_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 2, v___x_638_);
lean_ctor_set(v___x_635_, 1, v___x_637_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_satExpr_627_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_theoryState_631_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_solverTimeBudgetMs_632_);
lean_ctor_set(v_reuseFailAlloc_643_, 5, v_roundBudget_633_);
lean_ctor_set_uint8(v_reuseFailAlloc_643_, sizeof(void*)*6, v_didChange_630_);
v___x_640_ = v_reuseFailAlloc_643_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_st_ref_put(v_a_612_, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v_hypQueue_628_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_611_ = stack[0].m_obj;
lean_object* v_a_612_ = stack[1].m_obj;
lean_object* v_a_613_ = stack[2].m_obj;
lean_object* v_a_614_ = stack[3].m_obj;
lean_object* v_a_615_ = stack[4].m_obj;
lean_object* v_a_616_ = stack[5].m_obj;
lean_object* v_a_617_ = stack[6].m_obj;
lean_object* v_a_618_ = stack[7].m_obj;
lean_object* v_a_619_ = stack[8].m_obj;
lean_object* v_a_620_ = stack[9].m_obj;
lean_object* v_a_621_ = stack[10].m_obj;
lean_object* v_a_622_ = stack[11].m_obj;
lean_object* v_a_623_ = stack[12].m_obj;
lean_object* v_a_624_ = stack[13].m_obj;
lean_object* v_res_645_;
v_res_645_ = l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps(v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
stack->m_obj
 = v_res_645_;
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
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(lean_object* v_a_662_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_662_ = stack[0].m_obj;
lean_object* v_res_666_;
v_res_666_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(v_a_662_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg___boxed(lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___redArg(v_a_667_);
lean_dec_ref(v_a_667_);
return v_res_669_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_tacticContext_685_; lean_object* v___x_686_; 
v_tacticContext_685_ = lean_ctor_get(v_a_670_, 2);
lean_inc_ref(v_tacticContext_685_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_tacticContext_685_);
return v___x_686_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_670_ = stack[0].m_obj;
lean_object* v_a_671_ = stack[1].m_obj;
lean_object* v_a_672_ = stack[2].m_obj;
lean_object* v_a_673_ = stack[3].m_obj;
lean_object* v_a_674_ = stack[4].m_obj;
lean_object* v_a_675_ = stack[5].m_obj;
lean_object* v_a_676_ = stack[6].m_obj;
lean_object* v_a_677_ = stack[7].m_obj;
lean_object* v_a_678_ = stack[8].m_obj;
lean_object* v_a_679_ = stack[9].m_obj;
lean_object* v_a_680_ = stack[10].m_obj;
lean_object* v_a_681_ = stack[11].m_obj;
lean_object* v_a_682_ = stack[12].m_obj;
lean_object* v_a_683_ = stack[13].m_obj;
lean_object* v_res_687_;
v_res_687_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext___boxed(lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getTacticContext(v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_703_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(lean_object* v_a_704_){
_start:
{
lean_object* v_tacticContext_706_; lean_object* v_config_707_; uint8_t v_uf_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_tacticContext_706_ = lean_ctor_get(v_a_704_, 2);
v_config_707_ = lean_ctor_get(v_tacticContext_706_, 5);
v_uf_708_ = lean_ctor_get_uint8(v_config_707_, sizeof(void*)*3 + 11);
v___x_709_ = lean_box(v_uf_708_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_704_ = stack[0].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___redArg(v_a_704_);
stack->m_obj
 = v_res_711_;
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
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_tacticContext_730_; lean_object* v_config_731_; uint8_t v_uf_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_tacticContext_730_ = lean_ctor_get(v_a_715_, 2);
v_config_731_ = lean_ctor_get(v_tacticContext_730_, 5);
v_uf_732_ = lean_ctor_get_uint8(v_config_731_, sizeof(void*)*3 + 11);
v___x_733_ = lean_box(v_uf_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_715_ = stack[0].m_obj;
lean_object* v_a_716_ = stack[1].m_obj;
lean_object* v_a_717_ = stack[2].m_obj;
lean_object* v_a_718_ = stack[3].m_obj;
lean_object* v_a_719_ = stack[4].m_obj;
lean_object* v_a_720_ = stack[5].m_obj;
lean_object* v_a_721_ = stack[6].m_obj;
lean_object* v_a_722_ = stack[7].m_obj;
lean_object* v_a_723_ = stack[8].m_obj;
lean_object* v_a_724_ = stack[9].m_obj;
lean_object* v_a_725_ = stack[10].m_obj;
lean_object* v_a_726_ = stack[11].m_obj;
lean_object* v_a_727_ = stack[12].m_obj;
lean_object* v_a_728_ = stack[13].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures___boxed(lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_Tactic_BVDecide_CegarM_hasRefinementProcedures(v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_751_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(lean_object* v_ms_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; lean_object* v_satExpr_756_; lean_object* v_hypQueue_757_; lean_object* v_usedHyps_758_; uint8_t v_didChange_759_; lean_object* v_theoryState_760_; lean_object* v_solverTimeBudgetMs_761_; lean_object* v_roundBudget_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
v___x_755_ = lean_st_ref_take(v_a_753_);
v_satExpr_756_ = lean_ctor_get(v___x_755_, 0);
v_hypQueue_757_ = lean_ctor_get(v___x_755_, 1);
v_usedHyps_758_ = lean_ctor_get(v___x_755_, 2);
v_didChange_759_ = lean_ctor_get_uint8(v___x_755_, sizeof(void*)*6);
v_theoryState_760_ = lean_ctor_get(v___x_755_, 3);
v_solverTimeBudgetMs_761_ = lean_ctor_get(v___x_755_, 4);
v_roundBudget_762_ = lean_ctor_get(v___x_755_, 5);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_764_ = v___x_755_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_roundBudget_762_);
lean_inc(v_solverTimeBudgetMs_761_);
lean_inc(v_theoryState_760_);
lean_inc(v_usedHyps_758_);
lean_inc(v_hypQueue_757_);
lean_inc(v_satExpr_756_);
lean_dec(v___x_755_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = lean_box(0);
v___x_767_ = lean_nat_sub(v_solverTimeBudgetMs_761_, v_ms_752_);
lean_dec(v_solverTimeBudgetMs_761_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 4, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_satExpr_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_hypQueue_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_usedHyps_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_theoryState_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_roundBudget_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_772_, sizeof(void*)*6, v_didChange_759_);
v___x_769_ = v_reuseFailAlloc_772_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_st_ref_put(v_a_753_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_766_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ms_752_ = stack[0].m_obj;
lean_object* v_a_753_ = stack[1].m_obj;
lean_object* v_res_774_;
v_res_774_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(v_ms_752_, v_a_753_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg___boxed(lean_object* v_ms_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime___redArg(v_ms_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec(v_ms_775_);
return v_res_778_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(lean_object* v_ms_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_satExpr_796_; lean_object* v_hypQueue_797_; lean_object* v_usedHyps_798_; uint8_t v_didChange_799_; lean_object* v_theoryState_800_; lean_object* v_solverTimeBudgetMs_801_; lean_object* v_roundBudget_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_813_; 
v___x_795_ = lean_st_ref_take(v_a_781_);
v_satExpr_796_ = lean_ctor_get(v___x_795_, 0);
v_hypQueue_797_ = lean_ctor_get(v___x_795_, 1);
v_usedHyps_798_ = lean_ctor_get(v___x_795_, 2);
v_didChange_799_ = lean_ctor_get_uint8(v___x_795_, sizeof(void*)*6);
v_theoryState_800_ = lean_ctor_get(v___x_795_, 3);
v_solverTimeBudgetMs_801_ = lean_ctor_get(v___x_795_, 4);
v_roundBudget_802_ = lean_ctor_get(v___x_795_, 5);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_813_ == 0)
{
v___x_804_ = v___x_795_;
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_roundBudget_802_);
lean_inc(v_solverTimeBudgetMs_801_);
lean_inc(v_theoryState_800_);
lean_inc(v_usedHyps_798_);
lean_inc(v_hypQueue_797_);
lean_inc(v_satExpr_796_);
lean_dec(v___x_795_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_nat_sub(v_solverTimeBudgetMs_801_, v_ms_779_);
lean_dec(v_solverTimeBudgetMs_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v___x_807_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_satExpr_796_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_hypQueue_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_usedHyps_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_theoryState_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 5, v_roundBudget_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_812_, sizeof(void*)*6, v_didChange_799_);
v___x_809_ = v_reuseFailAlloc_812_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_st_ref_put(v_a_781_, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_806_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_ms_779_ = stack[0].m_obj;
lean_object* v_a_780_ = stack[1].m_obj;
lean_object* v_a_781_ = stack[2].m_obj;
lean_object* v_a_782_ = stack[3].m_obj;
lean_object* v_a_783_ = stack[4].m_obj;
lean_object* v_a_784_ = stack[5].m_obj;
lean_object* v_a_785_ = stack[6].m_obj;
lean_object* v_a_786_ = stack[7].m_obj;
lean_object* v_a_787_ = stack[8].m_obj;
lean_object* v_a_788_ = stack[9].m_obj;
lean_object* v_a_789_ = stack[10].m_obj;
lean_object* v_a_790_ = stack[11].m_obj;
lean_object* v_a_791_ = stack[12].m_obj;
lean_object* v_a_792_ = stack[13].m_obj;
lean_object* v_a_793_ = stack[14].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeSolverTime(v_ms_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
stack->m_obj
 = v_res_814_;
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
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(lean_object* v_a_832_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_832_ = stack[0].m_obj;
lean_object* v_res_837_;
v_res_837_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(v_a_832_);
stack->m_obj
 = v_res_837_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg___boxed(lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___redArg(v_a_838_);
lean_dec(v_a_838_);
return v_res_840_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_856_; lean_object* v_solverTimeBudgetMs_857_; lean_object* v___x_858_; 
v___x_856_ = lean_st_ref_get(v_a_842_);
v_solverTimeBudgetMs_857_ = lean_ctor_get(v___x_856_, 4);
lean_inc(v_solverTimeBudgetMs_857_);
lean_dec(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v_solverTimeBudgetMs_857_);
return v___x_858_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_841_ = stack[0].m_obj;
lean_object* v_a_842_ = stack[1].m_obj;
lean_object* v_a_843_ = stack[2].m_obj;
lean_object* v_a_844_ = stack[3].m_obj;
lean_object* v_a_845_ = stack[4].m_obj;
lean_object* v_a_846_ = stack[5].m_obj;
lean_object* v_a_847_ = stack[6].m_obj;
lean_object* v_a_848_ = stack[7].m_obj;
lean_object* v_a_849_ = stack[8].m_obj;
lean_object* v_a_850_ = stack[9].m_obj;
lean_object* v_a_851_ = stack[10].m_obj;
lean_object* v_a_852_ = stack[11].m_obj;
lean_object* v_a_853_ = stack[12].m_obj;
lean_object* v_a_854_ = stack[13].m_obj;
lean_object* v_res_859_;
v_res_859_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime___boxed(lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSolverTime(v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
return v_res_875_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; lean_object* v_satExpr_879_; lean_object* v_hypQueue_880_; lean_object* v_usedHyps_881_; uint8_t v_didChange_882_; lean_object* v_theoryState_883_; lean_object* v_solverTimeBudgetMs_884_; lean_object* v_roundBudget_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v___x_878_ = lean_st_ref_take(v_a_876_);
v_satExpr_879_ = lean_ctor_get(v___x_878_, 0);
v_hypQueue_880_ = lean_ctor_get(v___x_878_, 1);
v_usedHyps_881_ = lean_ctor_get(v___x_878_, 2);
v_didChange_882_ = lean_ctor_get_uint8(v___x_878_, sizeof(void*)*6);
v_theoryState_883_ = lean_ctor_get(v___x_878_, 3);
v_solverTimeBudgetMs_884_ = lean_ctor_get(v___x_878_, 4);
v_roundBudget_885_ = lean_ctor_get(v___x_878_, 5);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v___x_878_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_roundBudget_885_);
lean_inc(v_solverTimeBudgetMs_884_);
lean_inc(v_theoryState_883_);
lean_inc(v_usedHyps_881_);
lean_inc(v_hypQueue_880_);
lean_inc(v_satExpr_879_);
lean_dec(v___x_878_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_sub(v_roundBudget_885_, v___x_890_);
lean_dec(v_roundBudget_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 5, v___x_891_);
v___x_893_ = v___x_887_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_satExpr_879_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_hypQueue_880_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_usedHyps_881_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_theoryState_883_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_solverTimeBudgetMs_884_);
lean_ctor_set(v_reuseFailAlloc_896_, 5, v___x_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_896_, sizeof(void*)*6, v_didChange_882_);
v___x_893_ = v_reuseFailAlloc_896_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_st_ref_put(v_a_876_, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_889_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_876_ = stack[0].m_obj;
lean_object* v_res_898_;
v_res_898_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(v_a_876_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg___boxed(lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___redArg(v_a_899_);
lean_dec(v_a_899_);
return v_res_901_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; lean_object* v_satExpr_918_; lean_object* v_hypQueue_919_; lean_object* v_usedHyps_920_; uint8_t v_didChange_921_; lean_object* v_theoryState_922_; lean_object* v_solverTimeBudgetMs_923_; lean_object* v_roundBudget_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_936_; 
v___x_917_ = lean_st_ref_take(v_a_903_);
v_satExpr_918_ = lean_ctor_get(v___x_917_, 0);
v_hypQueue_919_ = lean_ctor_get(v___x_917_, 1);
v_usedHyps_920_ = lean_ctor_get(v___x_917_, 2);
v_didChange_921_ = lean_ctor_get_uint8(v___x_917_, sizeof(void*)*6);
v_theoryState_922_ = lean_ctor_get(v___x_917_, 3);
v_solverTimeBudgetMs_923_ = lean_ctor_get(v___x_917_, 4);
v_roundBudget_924_ = lean_ctor_get(v___x_917_, 5);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_936_ == 0)
{
v___x_926_ = v___x_917_;
v_isShared_927_ = v_isSharedCheck_936_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_roundBudget_924_);
lean_inc(v_solverTimeBudgetMs_923_);
lean_inc(v_theoryState_922_);
lean_inc(v_usedHyps_920_);
lean_inc(v_hypQueue_919_);
lean_inc(v_satExpr_918_);
lean_dec(v___x_917_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_936_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_928_ = lean_box(0);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v_roundBudget_924_, v___x_929_);
lean_dec(v_roundBudget_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 5, v___x_930_);
v___x_932_ = v___x_926_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_satExpr_918_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_hypQueue_919_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_usedHyps_920_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_theoryState_922_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_solverTimeBudgetMs_923_);
lean_ctor_set(v_reuseFailAlloc_935_, 5, v___x_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_935_, sizeof(void*)*6, v_didChange_921_);
v___x_932_ = v_reuseFailAlloc_935_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_st_ref_put(v_a_903_, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_928_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_902_ = stack[0].m_obj;
lean_object* v_a_903_ = stack[1].m_obj;
lean_object* v_a_904_ = stack[2].m_obj;
lean_object* v_a_905_ = stack[3].m_obj;
lean_object* v_a_906_ = stack[4].m_obj;
lean_object* v_a_907_ = stack[5].m_obj;
lean_object* v_a_908_ = stack[6].m_obj;
lean_object* v_a_909_ = stack[7].m_obj;
lean_object* v_a_910_ = stack[8].m_obj;
lean_object* v_a_911_ = stack[9].m_obj;
lean_object* v_a_912_ = stack[10].m_obj;
lean_object* v_a_913_ = stack[11].m_obj;
lean_object* v_a_914_ = stack[12].m_obj;
lean_object* v_a_915_ = stack[13].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound___boxed(lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Meta_Tactic_BVDecide_CegarM_consumeRound(v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_953_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; lean_object* v_roundBudget_957_; lean_object* v___x_958_; 
v___x_956_ = lean_st_ref_get(v_a_954_);
v_roundBudget_957_ = lean_ctor_get(v___x_956_, 5);
lean_inc(v_roundBudget_957_);
lean_dec(v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_roundBudget_957_);
return v___x_958_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_954_ = stack[0].m_obj;
lean_object* v_res_959_;
v_res_959_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(v_a_954_);
stack->m_obj
 = v_res_959_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg___boxed(lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___redArg(v_a_960_);
lean_dec(v_a_960_);
return v_res_962_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_roundBudget_979_; lean_object* v___x_980_; 
v___x_978_ = lean_st_ref_get(v_a_964_);
v_roundBudget_979_ = lean_ctor_get(v___x_978_, 5);
lean_inc(v_roundBudget_979_);
lean_dec(v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_roundBudget_979_);
return v___x_980_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_963_ = stack[0].m_obj;
lean_object* v_a_964_ = stack[1].m_obj;
lean_object* v_a_965_ = stack[2].m_obj;
lean_object* v_a_966_ = stack[3].m_obj;
lean_object* v_a_967_ = stack[4].m_obj;
lean_object* v_a_968_ = stack[5].m_obj;
lean_object* v_a_969_ = stack[6].m_obj;
lean_object* v_a_970_ = stack[7].m_obj;
lean_object* v_a_971_ = stack[8].m_obj;
lean_object* v_a_972_ = stack[9].m_obj;
lean_object* v_a_973_ = stack[10].m_obj;
lean_object* v_a_974_ = stack[11].m_obj;
lean_object* v_a_975_ = stack[12].m_obj;
lean_object* v_a_976_ = stack[13].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds___boxed(lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getRounds(v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
return v_res_997_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v_theoryState_1001_; lean_object* v_satExpr_1002_; lean_object* v_hypQueue_1003_; lean_object* v_usedHyps_1004_; uint8_t v_didChange_1005_; lean_object* v_solverTimeBudgetMs_1006_; lean_object* v_roundBudget_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1028_; 
v___x_1000_ = lean_st_ref_take(v_a_998_);
v_theoryState_1001_ = lean_ctor_get(v___x_1000_, 3);
v_satExpr_1002_ = lean_ctor_get(v___x_1000_, 0);
v_hypQueue_1003_ = lean_ctor_get(v___x_1000_, 1);
v_usedHyps_1004_ = lean_ctor_get(v___x_1000_, 2);
v_didChange_1005_ = lean_ctor_get_uint8(v___x_1000_, sizeof(void*)*6);
v_solverTimeBudgetMs_1006_ = lean_ctor_get(v___x_1000_, 4);
v_roundBudget_1007_ = lean_ctor_get(v___x_1000_, 5);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1009_ = v___x_1000_;
v_isShared_1010_ = v_isSharedCheck_1028_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_roundBudget_1007_);
lean_inc(v_solverTimeBudgetMs_1006_);
lean_inc(v_theoryState_1001_);
lean_inc(v_usedHyps_1004_);
lean_inc(v_hypQueue_1003_);
lean_inc(v_satExpr_1002_);
lean_dec(v___x_1000_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1028_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v_funState_1011_; lean_object* v_bitvecState_1012_; lean_object* v_preprocessCaches_1013_; lean_object* v_satSolver_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1027_; 
v_funState_1011_ = lean_ctor_get(v_theoryState_1001_, 0);
v_bitvecState_1012_ = lean_ctor_get(v_theoryState_1001_, 1);
v_preprocessCaches_1013_ = lean_ctor_get(v_theoryState_1001_, 2);
v_satSolver_1014_ = lean_ctor_get(v_theoryState_1001_, 3);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_theoryState_1001_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1016_ = v_theoryState_1001_;
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_satSolver_1014_);
lean_inc(v_preprocessCaches_1013_);
lean_inc(v_bitvecState_1012_);
lean_inc(v_funState_1011_);
lean_dec(v_theoryState_1001_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 2, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_funState_1011_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_bitvecState_1012_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_satSolver_1014_);
v___x_1020_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 3, v___x_1020_);
v___x_1022_ = v___x_1009_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_satExpr_1002_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_hypQueue_1003_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_usedHyps_1004_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_solverTimeBudgetMs_1006_);
lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_roundBudget_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*6, v_didChange_1005_);
v___x_1022_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_st_ref_put(v_a_998_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_preprocessCaches_1013_);
return v___x_1024_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_998_ = stack[0].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(v_a_998_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg___boxed(lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___redArg(v_a_1030_);
lean_dec(v_a_1030_);
return v_res_1032_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v_theoryState_1049_; lean_object* v_satExpr_1050_; lean_object* v_hypQueue_1051_; lean_object* v_usedHyps_1052_; uint8_t v_didChange_1053_; lean_object* v_solverTimeBudgetMs_1054_; lean_object* v_roundBudget_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1076_; 
v___x_1048_ = lean_st_ref_take(v_a_1034_);
v_theoryState_1049_ = lean_ctor_get(v___x_1048_, 3);
v_satExpr_1050_ = lean_ctor_get(v___x_1048_, 0);
v_hypQueue_1051_ = lean_ctor_get(v___x_1048_, 1);
v_usedHyps_1052_ = lean_ctor_get(v___x_1048_, 2);
v_didChange_1053_ = lean_ctor_get_uint8(v___x_1048_, sizeof(void*)*6);
v_solverTimeBudgetMs_1054_ = lean_ctor_get(v___x_1048_, 4);
v_roundBudget_1055_ = lean_ctor_get(v___x_1048_, 5);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1057_ = v___x_1048_;
v_isShared_1058_ = v_isSharedCheck_1076_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_roundBudget_1055_);
lean_inc(v_solverTimeBudgetMs_1054_);
lean_inc(v_theoryState_1049_);
lean_inc(v_usedHyps_1052_);
lean_inc(v_hypQueue_1051_);
lean_inc(v_satExpr_1050_);
lean_dec(v___x_1048_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1076_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_funState_1059_; lean_object* v_bitvecState_1060_; lean_object* v_preprocessCaches_1061_; lean_object* v_satSolver_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1075_; 
v_funState_1059_ = lean_ctor_get(v_theoryState_1049_, 0);
v_bitvecState_1060_ = lean_ctor_get(v_theoryState_1049_, 1);
v_preprocessCaches_1061_ = lean_ctor_get(v_theoryState_1049_, 2);
v_satSolver_1062_ = lean_ctor_get(v_theoryState_1049_, 3);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_theoryState_1049_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1064_ = v_theoryState_1049_;
v_isShared_1065_ = v_isSharedCheck_1075_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_satSolver_1062_);
lean_inc(v_preprocessCaches_1061_);
lean_inc(v_bitvecState_1060_);
lean_inc(v_funState_1059_);
lean_dec(v_theoryState_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1075_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__6);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 2, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_funState_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_bitvecState_1060_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_satSolver_1062_);
v___x_1068_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 3, v___x_1068_);
v___x_1070_ = v___x_1057_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_satExpr_1050_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_hypQueue_1051_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_usedHyps_1052_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_solverTimeBudgetMs_1054_);
lean_ctor_set(v_reuseFailAlloc_1073_, 5, v_roundBudget_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*6, v_didChange_1053_);
v___x_1070_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_st_ref_put(v_a_1034_, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_preprocessCaches_1061_);
return v___x_1072_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1033_ = stack[0].m_obj;
lean_object* v_a_1034_ = stack[1].m_obj;
lean_object* v_a_1035_ = stack[2].m_obj;
lean_object* v_a_1036_ = stack[3].m_obj;
lean_object* v_a_1037_ = stack[4].m_obj;
lean_object* v_a_1038_ = stack[5].m_obj;
lean_object* v_a_1039_ = stack[6].m_obj;
lean_object* v_a_1040_ = stack[7].m_obj;
lean_object* v_a_1041_ = stack[8].m_obj;
lean_object* v_a_1042_ = stack[9].m_obj;
lean_object* v_a_1043_ = stack[10].m_obj;
lean_object* v_a_1044_ = stack[11].m_obj;
lean_object* v_a_1045_ = stack[12].m_obj;
lean_object* v_a_1046_ = stack[13].m_obj;
lean_object* v_res_1077_;
v_res_1077_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
stack->m_obj
 = v_res_1077_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches___boxed(lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Meta_Tactic_BVDecide_CegarM_takePreProcessCaches(v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1093_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(lean_object* v_caches_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v_theoryState_1098_; lean_object* v_satExpr_1099_; lean_object* v_hypQueue_1100_; lean_object* v_usedHyps_1101_; uint8_t v_didChange_1102_; lean_object* v_solverTimeBudgetMs_1103_; lean_object* v_roundBudget_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1125_; 
v___x_1097_ = lean_st_ref_take(v_a_1095_);
v_theoryState_1098_ = lean_ctor_get(v___x_1097_, 3);
v_satExpr_1099_ = lean_ctor_get(v___x_1097_, 0);
v_hypQueue_1100_ = lean_ctor_get(v___x_1097_, 1);
v_usedHyps_1101_ = lean_ctor_get(v___x_1097_, 2);
v_didChange_1102_ = lean_ctor_get_uint8(v___x_1097_, sizeof(void*)*6);
v_solverTimeBudgetMs_1103_ = lean_ctor_get(v___x_1097_, 4);
v_roundBudget_1104_ = lean_ctor_get(v___x_1097_, 5);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1106_ = v___x_1097_;
v_isShared_1107_ = v_isSharedCheck_1125_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_roundBudget_1104_);
lean_inc(v_solverTimeBudgetMs_1103_);
lean_inc(v_theoryState_1098_);
lean_inc(v_usedHyps_1101_);
lean_inc(v_hypQueue_1100_);
lean_inc(v_satExpr_1099_);
lean_dec(v___x_1097_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1125_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_funState_1108_; lean_object* v_bitvecState_1109_; lean_object* v_satSolver_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1123_; 
v_funState_1108_ = lean_ctor_get(v_theoryState_1098_, 0);
v_bitvecState_1109_ = lean_ctor_get(v_theoryState_1098_, 1);
v_satSolver_1110_ = lean_ctor_get(v_theoryState_1098_, 3);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_theoryState_1098_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_theoryState_1098_, 2);
lean_dec(v_unused_1124_);
v___x_1112_ = v_theoryState_1098_;
v_isShared_1113_ = v_isSharedCheck_1123_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_satSolver_1110_);
lean_inc(v_bitvecState_1109_);
lean_inc(v_funState_1108_);
lean_dec(v_theoryState_1098_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1123_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 2, v_caches_1094_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_funState_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_bitvecState_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_caches_1094_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_satSolver_1110_);
v___x_1116_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 3, v___x_1116_);
v___x_1118_ = v___x_1106_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_satExpr_1099_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_hypQueue_1100_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_usedHyps_1101_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_solverTimeBudgetMs_1103_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_roundBudget_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6, v_didChange_1102_);
v___x_1118_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_st_ref_put(v_a_1095_, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1114_);
return v___x_1120_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_1094_ = stack[0].m_obj;
lean_object* v_a_1095_ = stack[1].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(v_caches_1094_, v_a_1095_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg___boxed(lean_object* v_caches_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___redArg(v_caches_1127_, v_a_1128_);
lean_dec(v_a_1128_);
return v_res_1130_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(lean_object* v_caches_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v_theoryState_1148_; lean_object* v_satExpr_1149_; lean_object* v_hypQueue_1150_; lean_object* v_usedHyps_1151_; uint8_t v_didChange_1152_; lean_object* v_solverTimeBudgetMs_1153_; lean_object* v_roundBudget_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1175_; 
v___x_1147_ = lean_st_ref_take(v_a_1133_);
v_theoryState_1148_ = lean_ctor_get(v___x_1147_, 3);
v_satExpr_1149_ = lean_ctor_get(v___x_1147_, 0);
v_hypQueue_1150_ = lean_ctor_get(v___x_1147_, 1);
v_usedHyps_1151_ = lean_ctor_get(v___x_1147_, 2);
v_didChange_1152_ = lean_ctor_get_uint8(v___x_1147_, sizeof(void*)*6);
v_solverTimeBudgetMs_1153_ = lean_ctor_get(v___x_1147_, 4);
v_roundBudget_1154_ = lean_ctor_get(v___x_1147_, 5);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1156_ = v___x_1147_;
v_isShared_1157_ = v_isSharedCheck_1175_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_roundBudget_1154_);
lean_inc(v_solverTimeBudgetMs_1153_);
lean_inc(v_theoryState_1148_);
lean_inc(v_usedHyps_1151_);
lean_inc(v_hypQueue_1150_);
lean_inc(v_satExpr_1149_);
lean_dec(v___x_1147_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1175_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_funState_1158_; lean_object* v_bitvecState_1159_; lean_object* v_satSolver_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1173_; 
v_funState_1158_ = lean_ctor_get(v_theoryState_1148_, 0);
v_bitvecState_1159_ = lean_ctor_get(v_theoryState_1148_, 1);
v_satSolver_1160_ = lean_ctor_get(v_theoryState_1148_, 3);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_theoryState_1148_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v_theoryState_1148_, 2);
lean_dec(v_unused_1174_);
v___x_1162_ = v_theoryState_1148_;
v_isShared_1163_ = v_isSharedCheck_1173_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_satSolver_1160_);
lean_inc(v_bitvecState_1159_);
lean_inc(v_funState_1158_);
lean_dec(v_theoryState_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1173_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 2, v_caches_1131_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_funState_1158_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_bitvecState_1159_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_caches_1131_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_satSolver_1160_);
v___x_1166_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 3, v___x_1166_);
v___x_1168_ = v___x_1156_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_satExpr_1149_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_hypQueue_1150_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_usedHyps_1151_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_solverTimeBudgetMs_1153_);
lean_ctor_set(v_reuseFailAlloc_1171_, 5, v_roundBudget_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*6, v_didChange_1152_);
v___x_1168_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_st_ref_put(v_a_1133_, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1164_);
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches_0interp(lean_interpreter_value* stack)
{
lean_object* v_caches_1131_ = stack[0].m_obj;
lean_object* v_a_1132_ = stack[1].m_obj;
lean_object* v_a_1133_ = stack[2].m_obj;
lean_object* v_a_1134_ = stack[3].m_obj;
lean_object* v_a_1135_ = stack[4].m_obj;
lean_object* v_a_1136_ = stack[5].m_obj;
lean_object* v_a_1137_ = stack[6].m_obj;
lean_object* v_a_1138_ = stack[7].m_obj;
lean_object* v_a_1139_ = stack[8].m_obj;
lean_object* v_a_1140_ = stack[9].m_obj;
lean_object* v_a_1141_ = stack[10].m_obj;
lean_object* v_a_1142_ = stack[11].m_obj;
lean_object* v_a_1143_ = stack[12].m_obj;
lean_object* v_a_1144_ = stack[13].m_obj;
lean_object* v_a_1145_ = stack[14].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(v_caches_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches___boxed(lean_object* v_caches_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_Tactic_BVDecide_CegarM_setPreProcessCaches(v_caches_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1193_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(lean_object* v_ctx_1194_, lean_object* v_x_1195_, lean_object* v_goal_1196_, lean_object* v_reflectionResult_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_config_1212_; lean_object* v_satExpr_1213_; lean_object* v_unusedHypotheses_1214_; lean_object* v_timeout_1215_; lean_object* v_cegarRounds_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1211_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1212_ = lean_ctor_get(v_ctx_1194_, 5);
v_satExpr_1213_ = lean_ctor_get(v_reflectionResult_1197_, 0);
v_unusedHypotheses_1214_ = lean_ctor_get(v_reflectionResult_1197_, 1);
v_timeout_1215_ = lean_ctor_get(v_config_1212_, 0);
v_cegarRounds_1216_ = lean_ctor_get(v_config_1212_, 2);
v___x_1217_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1218_ = 1;
v___x_1219_ = lean_unsigned_to_nat(1000u);
v___x_1220_ = lean_nat_mul(v_timeout_1215_, v___x_1219_);
lean_inc(v_cegarRounds_1216_);
lean_inc_ref(v_satExpr_1213_);
v___x_1221_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1221_, 0, v_satExpr_1213_);
lean_ctor_set(v___x_1221_, 1, v___x_1217_);
lean_ctor_set(v___x_1221_, 2, v___x_1217_);
lean_ctor_set(v___x_1221_, 3, v___x_1211_);
lean_ctor_set(v___x_1221_, 4, v___x_1220_);
lean_ctor_set(v___x_1221_, 5, v_cegarRounds_1216_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*6, v___x_1218_);
lean_inc_ref(v_unusedHypotheses_1214_);
v___x_1222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1222_, 0, v_goal_1196_);
lean_ctor_set(v___x_1222_, 1, v_unusedHypotheses_1214_);
lean_ctor_set(v___x_1222_, 2, v_ctx_1194_);
v___x_1223_ = lean_st_mk_ref(v___x_1221_);
lean_inc(v_a_1209_);
lean_inc_ref(v_a_1208_);
lean_inc(v_a_1207_);
lean_inc_ref(v_a_1206_);
lean_inc(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
lean_inc(v_a_1198_);
lean_inc(v___x_1223_);
v___x_1224_ = lean_apply_15(v_x_1195_, v___x_1222_, v___x_1223_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, lean_box(0));
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_st_ref_get(v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v___x_1229_);
if (v_isShared_1228_ == 0)
{
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1225_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_dec(v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1194_ = stack[0].m_obj;
lean_object* v_x_1195_ = stack[1].m_obj;
lean_object* v_goal_1196_ = stack[2].m_obj;
lean_object* v_reflectionResult_1197_ = stack[3].m_obj;
lean_object* v_a_1198_ = stack[4].m_obj;
lean_object* v_a_1199_ = stack[5].m_obj;
lean_object* v_a_1200_ = stack[6].m_obj;
lean_object* v_a_1201_ = stack[7].m_obj;
lean_object* v_a_1202_ = stack[8].m_obj;
lean_object* v_a_1203_ = stack[9].m_obj;
lean_object* v_a_1204_ = stack[10].m_obj;
lean_object* v_a_1205_ = stack[11].m_obj;
lean_object* v_a_1206_ = stack[12].m_obj;
lean_object* v_a_1207_ = stack[13].m_obj;
lean_object* v_a_1208_ = stack[14].m_obj;
lean_object* v_a_1209_ = stack[15].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(v_ctx_1194_, v_x_1195_, v_goal_1196_, v_reflectionResult_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg___boxed(lean_object** _args){
lean_object* v_ctx_1235_ = _args[0];
lean_object* v_x_1236_ = _args[1];
lean_object* v_goal_1237_ = _args[2];
lean_object* v_reflectionResult_1238_ = _args[3];
lean_object* v_a_1239_ = _args[4];
lean_object* v_a_1240_ = _args[5];
lean_object* v_a_1241_ = _args[6];
lean_object* v_a_1242_ = _args[7];
lean_object* v_a_1243_ = _args[8];
lean_object* v_a_1244_ = _args[9];
lean_object* v_a_1245_ = _args[10];
lean_object* v_a_1246_ = _args[11];
lean_object* v_a_1247_ = _args[12];
lean_object* v_a_1248_ = _args[13];
lean_object* v_a_1249_ = _args[14];
lean_object* v_a_1250_ = _args[15];
lean_object* v_a_1251_ = _args[16];
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run___redArg(v_ctx_1235_, v_x_1236_, v_goal_1237_, v_reflectionResult_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_reflectionResult_1238_);
return v_res_1252_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_object* v_00_u03b1_1253_, lean_object* v_ctx_1254_, lean_object* v_x_1255_, lean_object* v_goal_1256_, lean_object* v_reflectionResult_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v_config_1272_; lean_object* v_satExpr_1273_; lean_object* v_unusedHypotheses_1274_; lean_object* v_timeout_1275_; lean_object* v_cegarRounds_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1271_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_1272_ = lean_ctor_get(v_ctx_1254_, 5);
v_satExpr_1273_ = lean_ctor_get(v_reflectionResult_1257_, 0);
v_unusedHypotheses_1274_ = lean_ctor_get(v_reflectionResult_1257_, 1);
v_timeout_1275_ = lean_ctor_get(v_config_1272_, 0);
v_cegarRounds_1276_ = lean_ctor_get(v_config_1272_, 2);
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1278_ = 1;
v___x_1279_ = lean_unsigned_to_nat(1000u);
v___x_1280_ = lean_nat_mul(v_timeout_1275_, v___x_1279_);
lean_inc(v_cegarRounds_1276_);
lean_inc_ref(v_satExpr_1273_);
v___x_1281_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1281_, 0, v_satExpr_1273_);
lean_ctor_set(v___x_1281_, 1, v___x_1277_);
lean_ctor_set(v___x_1281_, 2, v___x_1277_);
lean_ctor_set(v___x_1281_, 3, v___x_1271_);
lean_ctor_set(v___x_1281_, 4, v___x_1280_);
lean_ctor_set(v___x_1281_, 5, v_cegarRounds_1276_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*6, v___x_1278_);
lean_inc_ref(v_unusedHypotheses_1274_);
v___x_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1282_, 0, v_goal_1256_);
lean_ctor_set(v___x_1282_, 1, v_unusedHypotheses_1274_);
lean_ctor_set(v___x_1282_, 2, v_ctx_1254_);
v___x_1283_ = lean_st_mk_ref(v___x_1281_);
lean_inc(v_a_1269_);
lean_inc_ref(v_a_1268_);
lean_inc(v_a_1267_);
lean_inc_ref(v_a_1266_);
lean_inc(v_a_1265_);
lean_inc_ref(v_a_1264_);
lean_inc(v_a_1263_);
lean_inc_ref(v_a_1262_);
lean_inc(v_a_1261_);
lean_inc(v_a_1260_);
lean_inc_ref(v_a_1259_);
lean_inc(v_a_1258_);
lean_inc(v___x_1283_);
v___x_1284_ = lean_apply_15(v_x_1255_, v___x_1282_, v___x_1283_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, lean_box(0));
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_st_ref_get(v___x_1283_);
lean_dec(v___x_1283_);
lean_dec(v___x_1289_);
if (v_isShared_1288_ == 0)
{
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1285_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_dec(v___x_1283_);
return v___x_1284_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1254_ = stack[1].m_obj;
lean_object* v_x_1255_ = stack[2].m_obj;
lean_object* v_goal_1256_ = stack[3].m_obj;
lean_object* v_reflectionResult_1257_ = stack[4].m_obj;
lean_object* v_a_1258_ = stack[5].m_obj;
lean_object* v_a_1259_ = stack[6].m_obj;
lean_object* v_a_1260_ = stack[7].m_obj;
lean_object* v_a_1261_ = stack[8].m_obj;
lean_object* v_a_1262_ = stack[9].m_obj;
lean_object* v_a_1263_ = stack[10].m_obj;
lean_object* v_a_1264_ = stack[11].m_obj;
lean_object* v_a_1265_ = stack[12].m_obj;
lean_object* v_a_1266_ = stack[13].m_obj;
lean_object* v_a_1267_ = stack[14].m_obj;
lean_object* v_a_1268_ = stack[15].m_obj;
lean_object* v_a_1269_ = stack[16].m_obj;
lean_object* v_res_1294_;
v_res_1294_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run(lean_box(0), v_ctx_1254_, v_x_1255_, v_goal_1256_, v_reflectionResult_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
stack->m_obj
 = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_run___boxed(lean_object** _args){
lean_object* v_00_u03b1_1295_ = _args[0];
lean_object* v_ctx_1296_ = _args[1];
lean_object* v_x_1297_ = _args[2];
lean_object* v_goal_1298_ = _args[3];
lean_object* v_reflectionResult_1299_ = _args[4];
lean_object* v_a_1300_ = _args[5];
lean_object* v_a_1301_ = _args[6];
lean_object* v_a_1302_ = _args[7];
lean_object* v_a_1303_ = _args[8];
lean_object* v_a_1304_ = _args[9];
lean_object* v_a_1305_ = _args[10];
lean_object* v_a_1306_ = _args[11];
lean_object* v_a_1307_ = _args[12];
lean_object* v_a_1308_ = _args[13];
lean_object* v_a_1309_ = _args[14];
lean_object* v_a_1310_ = _args[15];
lean_object* v_a_1311_ = _args[16];
lean_object* v_a_1312_ = _args[17];
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Meta_Tactic_BVDecide_CegarM_run(v_00_u03b1_1295_, v_ctx_1296_, v_x_1297_, v_goal_1298_, v_reflectionResult_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_reflectionResult_1299_);
return v_res_1313_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v_theoryState_1317_; lean_object* v_satSolver_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_st_ref_get(v_a_1314_);
v_theoryState_1317_ = lean_ctor_get(v___x_1316_, 3);
lean_inc_ref(v_theoryState_1317_);
lean_dec(v___x_1316_);
v_satSolver_1318_ = lean_ctor_get(v_theoryState_1317_, 3);
lean_inc_ref(v_satSolver_1318_);
lean_dec_ref(v_theoryState_1317_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_satSolver_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1314_ = stack[0].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1314_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg___boxed(lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1321_);
lean_dec(v_a_1321_);
return v_res_1323_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1325_);
return v___x_1339_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1324_ = stack[0].m_obj;
lean_object* v_a_1325_ = stack[1].m_obj;
lean_object* v_a_1326_ = stack[2].m_obj;
lean_object* v_a_1327_ = stack[3].m_obj;
lean_object* v_a_1328_ = stack[4].m_obj;
lean_object* v_a_1329_ = stack[5].m_obj;
lean_object* v_a_1330_ = stack[6].m_obj;
lean_object* v_a_1331_ = stack[7].m_obj;
lean_object* v_a_1332_ = stack[8].m_obj;
lean_object* v_a_1333_ = stack[9].m_obj;
lean_object* v_a_1334_ = stack[10].m_obj;
lean_object* v_a_1335_ = stack[11].m_obj;
lean_object* v_a_1336_ = stack[12].m_obj;
lean_object* v_a_1337_ = stack[13].m_obj;
lean_object* v_res_1340_;
v_res_1340_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
stack->m_obj
 = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___boxed(lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver(v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
return v_res_1356_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_instMonadEIO___redArg();
return v___x_1357_;
}
}
lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(lean_object* v_msg_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_toApplicative_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1445_; 
v___x_1375_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__0);
v___x_1376_ = l_StateRefT_x27_instMonad___redArg(v___x_1375_);
v_toApplicative_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1376_, 1);
lean_dec(v_unused_1446_);
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1445_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_toApplicative_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1445_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_toFunctor_1381_; lean_object* v_toSeq_1382_; lean_object* v_toSeqLeft_1383_; lean_object* v_toSeqRight_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1443_; 
v_toFunctor_1381_ = lean_ctor_get(v_toApplicative_1377_, 0);
v_toSeq_1382_ = lean_ctor_get(v_toApplicative_1377_, 2);
v_toSeqLeft_1383_ = lean_ctor_get(v_toApplicative_1377_, 3);
v_toSeqRight_1384_ = lean_ctor_get(v_toApplicative_1377_, 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_toApplicative_1377_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_toApplicative_1377_, 1);
lean_dec(v_unused_1444_);
v___x_1386_ = v_toApplicative_1377_;
v_isShared_1387_ = v_isSharedCheck_1443_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_toSeqRight_1384_);
lean_inc(v_toSeqLeft_1383_);
lean_inc(v_toSeq_1382_);
lean_inc(v_toFunctor_1381_);
lean_dec(v_toApplicative_1377_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1443_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___f_1388_; lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___f_1393_; lean_object* v___f_1394_; lean_object* v___f_1395_; lean_object* v___x_1397_; 
v___f_1388_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__1));
v___f_1389_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__2));
lean_inc_ref(v_toFunctor_1381_);
v___f_1390_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1390_, 0, v_toFunctor_1381_);
v___f_1391_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1391_, 0, v_toFunctor_1381_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___f_1390_);
lean_ctor_set(v___x_1392_, 1, v___f_1391_);
v___f_1393_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1393_, 0, v_toSeqRight_1384_);
v___f_1394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1394_, 0, v_toSeqLeft_1383_);
v___f_1395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1395_, 0, v_toSeq_1382_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___f_1393_);
lean_ctor_set(v___x_1386_, 3, v___f_1394_);
lean_ctor_set(v___x_1386_, 2, v___f_1395_);
lean_ctor_set(v___x_1386_, 1, v___f_1388_);
lean_ctor_set(v___x_1386_, 0, v___x_1392_);
v___x_1397_ = v___x_1386_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___f_1388_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___f_1395_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v___f_1394_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___f_1393_);
v___x_1397_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___f_1389_);
lean_ctor_set(v___x_1379_, 0, v___x_1397_);
v___x_1399_ = v___x_1379_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___f_1389_);
v___x_1399_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v_toApplicative_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1439_; 
v___x_1400_ = l_StateRefT_x27_instMonad___redArg(v___x_1399_);
v_toApplicative_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1400_, 1);
lean_dec(v_unused_1440_);
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1439_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_toApplicative_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1439_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_toFunctor_1405_; lean_object* v_toSeq_1406_; lean_object* v_toSeqLeft_1407_; lean_object* v_toSeqRight_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1437_; 
v_toFunctor_1405_ = lean_ctor_get(v_toApplicative_1401_, 0);
v_toSeq_1406_ = lean_ctor_get(v_toApplicative_1401_, 2);
v_toSeqLeft_1407_ = lean_ctor_get(v_toApplicative_1401_, 3);
v_toSeqRight_1408_ = lean_ctor_get(v_toApplicative_1401_, 4);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_toApplicative_1401_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_toApplicative_1401_, 1);
lean_dec(v_unused_1438_);
v___x_1410_ = v_toApplicative_1401_;
v_isShared_1411_ = v_isSharedCheck_1437_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_toSeqRight_1408_);
lean_inc(v_toSeqLeft_1407_);
lean_inc(v_toSeq_1406_);
lean_inc(v_toFunctor_1405_);
lean_dec(v_toApplicative_1401_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1437_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___f_1419_; lean_object* v___x_1421_; 
v___f_1412_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__3));
v___f_1413_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___closed__4));
lean_inc_ref(v_toFunctor_1405_);
v___f_1414_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1414_, 0, v_toFunctor_1405_);
v___f_1415_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1415_, 0, v_toFunctor_1405_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___f_1414_);
lean_ctor_set(v___x_1416_, 1, v___f_1415_);
v___f_1417_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1417_, 0, v_toSeqRight_1408_);
v___f_1418_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1418_, 0, v_toSeqLeft_1407_);
v___f_1419_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1419_, 0, v_toSeq_1406_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v___f_1417_);
lean_ctor_set(v___x_1410_, 3, v___f_1418_);
lean_ctor_set(v___x_1410_, 2, v___f_1419_);
lean_ctor_set(v___x_1410_, 1, v___f_1412_);
lean_ctor_set(v___x_1410_, 0, v___x_1416_);
v___x_1421_ = v___x_1410_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___f_1412_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v___f_1419_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v___f_1418_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v___f_1417_);
v___x_1421_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___f_1413_);
lean_ctor_set(v___x_1403_, 0, v___x_1421_);
v___x_1423_ = v___x_1403_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___f_1413_);
v___x_1423_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_4587__overap_1433_; lean_object* v___x_1434_; 
v___x_1424_ = l_StateRefT_x27_instMonad___redArg(v___x_1423_);
v___x_1425_ = l_ReaderT_instMonad___redArg(v___x_1424_);
v___x_1426_ = l_StateRefT_x27_instMonad___redArg(v___x_1425_);
v___x_1427_ = l_ReaderT_instMonad___redArg(v___x_1426_);
v___x_1428_ = l_ReaderT_instMonad___redArg(v___x_1427_);
v___x_1429_ = l_StateRefT_x27_instMonad___redArg(v___x_1428_);
v___x_1430_ = lean_box(0);
v___x_1431_ = l_instInhabitedOfMonad___redArg(v___x_1429_, v___x_1430_);
v___f_1432_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1432_, 0, v___x_1431_);
v___x_4587__overap_1433_ = lean_panic_fn_borrowed(v___f_1432_, v_msg_1362_);
lean_dec_ref(v___f_1432_);
lean_inc(v___y_1373_);
lean_inc_ref(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc_ref(v___y_1368_);
lean_inc(v___y_1367_);
lean_inc_ref(v___y_1366_);
lean_inc(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
v___x_1434_ = lean_apply_12(v___x_4587__overap_1433_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, lean_box(0));
return v___x_1434_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1362_ = stack[0].m_obj;
lean_object* v___y_1363_ = stack[1].m_obj;
lean_object* v___y_1364_ = stack[2].m_obj;
lean_object* v___y_1365_ = stack[3].m_obj;
lean_object* v___y_1366_ = stack[4].m_obj;
lean_object* v___y_1367_ = stack[5].m_obj;
lean_object* v___y_1368_ = stack[6].m_obj;
lean_object* v___y_1369_ = stack[7].m_obj;
lean_object* v___y_1370_ = stack[8].m_obj;
lean_object* v___y_1371_ = stack[9].m_obj;
lean_object* v___y_1372_ = stack[10].m_obj;
lean_object* v___y_1373_ = stack[11].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v_msg_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2___boxed(lean_object* v_msg_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v_msg_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
return v_x_1462_;
}
else
{
lean_object* v_key_1464_; lean_object* v_value_1465_; lean_object* v_tail_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1489_; 
v_key_1464_ = lean_ctor_get(v_x_1463_, 0);
v_value_1465_ = lean_ctor_get(v_x_1463_, 1);
v_tail_1466_ = lean_ctor_get(v_x_1463_, 2);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1468_ = v_x_1463_;
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_tail_1466_);
lean_inc(v_value_1465_);
lean_inc(v_key_1464_);
lean_dec(v_x_1463_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; uint64_t v___x_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v_fold_1474_; uint64_t v___x_1475_; uint64_t v___x_1476_; uint64_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1470_ = lean_array_get_size(v_x_1462_);
v___x_1471_ = l_Lean_Expr_hash(v_key_1464_);
v___x_1472_ = 32ULL;
v___x_1473_ = lean_uint64_shift_right(v___x_1471_, v___x_1472_);
v_fold_1474_ = lean_uint64_xor(v___x_1471_, v___x_1473_);
v___x_1475_ = 16ULL;
v___x_1476_ = lean_uint64_shift_right(v_fold_1474_, v___x_1475_);
v___x_1477_ = lean_uint64_xor(v_fold_1474_, v___x_1476_);
v___x_1478_ = lean_uint64_to_usize(v___x_1477_);
v___x_1479_ = lean_usize_of_nat(v___x_1470_);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_sub(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_usize_land(v___x_1478_, v___x_1481_);
v___x_1483_ = lean_array_uget_borrowed(v_x_1462_, v___x_1482_);
lean_inc(v___x_1483_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 2, v___x_1483_);
v___x_1485_ = v___x_1468_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_key_1464_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_value_1465_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_array_uset(v_x_1462_, v___x_1482_, v___x_1485_);
v_x_1462_ = v___x_1486_;
v_x_1463_ = v_tail_1466_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(lean_object* v_i_1490_, lean_object* v_source_1491_, lean_object* v_target_1492_){
_start:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_array_get_size(v_source_1491_);
v___x_1494_ = lean_nat_dec_lt(v_i_1490_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_dec_ref(v_source_1491_);
lean_dec(v_i_1490_);
return v_target_1492_;
}
else
{
lean_object* v_es_1495_; lean_object* v___x_1496_; lean_object* v_source_1497_; lean_object* v_target_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_es_1495_ = lean_array_fget(v_source_1491_, v_i_1490_);
v___x_1496_ = lean_box(0);
v_source_1497_ = lean_array_fset(v_source_1491_, v_i_1490_, v___x_1496_);
v_target_1498_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_target_1492_, v_es_1495_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1490_, v___x_1499_);
lean_dec(v_i_1490_);
v_i_1490_ = v___x_1500_;
v_source_1491_ = v_source_1497_;
v_target_1492_ = v_target_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(lean_object* v_data_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_nbuckets_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1503_ = lean_array_get_size(v_data_1502_);
v___x_1504_ = lean_unsigned_to_nat(2u);
v_nbuckets_1505_ = lean_nat_mul(v___x_1503_, v___x_1504_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_mk_array(v_nbuckets_1505_, v___x_1507_);
v___x_1509_ = lean_array_propagate_mark(v_data_1502_, v___x_1508_);
v___x_1510_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v___x_1506_, v_data_1502_, v___x_1509_);
return v___x_1510_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(lean_object* v_a_1511_, lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 0)
{
uint8_t v___x_1513_; 
v___x_1513_ = 0;
return v___x_1513_;
}
else
{
lean_object* v_key_1514_; lean_object* v_tail_1515_; uint8_t v___x_1516_; 
v_key_1514_ = lean_ctor_get(v_x_1512_, 0);
v_tail_1515_ = lean_ctor_get(v_x_1512_, 2);
v___x_1516_ = lean_expr_eqv(v_key_1514_, v_a_1511_);
if (v___x_1516_ == 0)
{
v_x_1512_ = v_tail_1515_;
goto _start;
}
else
{
return v___x_1516_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1511_ = stack[0].m_obj;
lean_object* v_x_1512_ = stack[1].m_obj;
uint8_t v_res_1518_;
v_res_1518_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1511_, v_x_1512_);
stack->m_num = v_res_1518_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg___boxed(lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1519_, v_x_1520_);
lean_dec(v_x_1520_);
lean_dec_ref(v_a_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(lean_object* v_a_1523_, lean_object* v_b_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_dec(v_b_1524_);
lean_dec_ref(v_a_1523_);
return v_x_1525_;
}
else
{
lean_object* v_key_1526_; lean_object* v_value_1527_; lean_object* v_tail_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1540_; 
v_key_1526_ = lean_ctor_get(v_x_1525_, 0);
v_value_1527_ = lean_ctor_get(v_x_1525_, 1);
v_tail_1528_ = lean_ctor_get(v_x_1525_, 2);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1530_ = v_x_1525_;
v_isShared_1531_ = v_isSharedCheck_1540_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_tail_1528_);
lean_inc(v_value_1527_);
lean_inc(v_key_1526_);
lean_dec(v_x_1525_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1540_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_expr_eqv(v_key_1526_, v_a_1523_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1523_, v_b_1524_, v_tail_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 2, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_key_1526_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_value_1527_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v___x_1533_);
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
lean_dec(v_value_1527_);
lean_dec(v_key_1526_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v_b_1524_);
lean_ctor_set(v___x_1530_, 0, v_a_1523_);
v___x_1538_ = v___x_1530_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1523_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_b_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_tail_1528_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(lean_object* v_m_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v_size_1544_; lean_object* v_buckets_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1588_; 
v_size_1544_ = lean_ctor_get(v_m_1541_, 0);
v_buckets_1545_ = lean_ctor_get(v_m_1541_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_m_1541_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1547_ = v_m_1541_;
v_isShared_1548_ = v_isSharedCheck_1588_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_buckets_1545_);
lean_inc(v_size_1544_);
lean_dec(v_m_1541_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1588_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; uint64_t v___x_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; uint64_t v_fold_1553_; uint64_t v___x_1554_; uint64_t v___x_1555_; uint64_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; size_t v___x_1561_; lean_object* v_bkt_1562_; uint8_t v___x_1563_; 
v___x_1549_ = lean_array_get_size(v_buckets_1545_);
v___x_1550_ = l_Lean_Expr_hash(v_a_1542_);
v___x_1551_ = 32ULL;
v___x_1552_ = lean_uint64_shift_right(v___x_1550_, v___x_1551_);
v_fold_1553_ = lean_uint64_xor(v___x_1550_, v___x_1552_);
v___x_1554_ = 16ULL;
v___x_1555_ = lean_uint64_shift_right(v_fold_1553_, v___x_1554_);
v___x_1556_ = lean_uint64_xor(v_fold_1553_, v___x_1555_);
v___x_1557_ = lean_uint64_to_usize(v___x_1556_);
v___x_1558_ = lean_usize_of_nat(v___x_1549_);
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_sub(v___x_1558_, v___x_1559_);
v___x_1561_ = lean_usize_land(v___x_1557_, v___x_1560_);
v_bkt_1562_ = lean_array_uget_borrowed(v_buckets_1545_, v___x_1561_);
v___x_1563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1542_, v_bkt_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v_size_x27_1565_; lean_object* v___x_1566_; lean_object* v_buckets_x27_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v_size_x27_1565_ = lean_nat_add(v_size_1544_, v___x_1564_);
lean_dec(v_size_1544_);
lean_inc(v_bkt_1562_);
v___x_1566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1542_);
lean_ctor_set(v___x_1566_, 1, v_b_1543_);
lean_ctor_set(v___x_1566_, 2, v_bkt_1562_);
v_buckets_x27_1567_ = lean_array_uset(v_buckets_1545_, v___x_1561_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(4u);
v___x_1569_ = lean_nat_mul(v_size_x27_1565_, v___x_1568_);
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = lean_nat_div(v___x_1569_, v___x_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_array_get_size(v_buckets_x27_1567_);
v___x_1573_ = lean_nat_dec_le(v___x_1571_, v___x_1572_);
lean_dec(v___x_1571_);
if (v___x_1573_ == 0)
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
v_val_1574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_buckets_x27_1567_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v_val_1574_);
lean_ctor_set(v___x_1547_, 0, v_size_x27_1565_);
v___x_1576_ = v___x_1547_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_size_x27_1565_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_val_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1579_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v_buckets_x27_1567_);
lean_ctor_set(v___x_1547_, 0, v_size_x27_1565_);
v___x_1579_ = v___x_1547_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_size_x27_1565_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_buckets_x27_1567_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_object* v___x_1581_; lean_object* v_buckets_x27_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_inc(v_bkt_1562_);
v___x_1581_ = lean_box(0);
v_buckets_x27_1582_ = lean_array_uset(v_buckets_1545_, v___x_1561_, v___x_1581_);
v___x_1583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1542_, v_b_1543_, v_bkt_1562_);
v___x_1584_ = lean_array_uset(v_buckets_x27_1582_, v___x_1561_, v___x_1583_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___x_1584_);
v___x_1586_ = v___x_1547_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_size_1544_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(lean_object* v_a_1589_, lean_object* v_b_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1591_) == 0)
{
lean_dec(v_b_1590_);
lean_dec(v_a_1589_);
return v_x_1591_;
}
else
{
lean_object* v_key_1592_; lean_object* v_value_1593_; lean_object* v_tail_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1606_; 
v_key_1592_ = lean_ctor_get(v_x_1591_, 0);
v_value_1593_ = lean_ctor_get(v_x_1591_, 1);
v_tail_1594_ = lean_ctor_get(v_x_1591_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1596_ = v_x_1591_;
v_isShared_1597_ = v_isSharedCheck_1606_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_tail_1594_);
lean_inc(v_value_1593_);
lean_inc(v_key_1592_);
lean_dec(v_x_1591_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1606_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_nat_dec_eq(v_key_1592_, v_a_1589_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1589_, v_b_1590_, v_tail_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 2, v___x_1599_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_key_1592_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_value_1593_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_value_1593_);
lean_dec(v_key_1592_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v_b_1590_);
lean_ctor_set(v___x_1596_, 0, v_a_1589_);
v___x_1604_ = v___x_1596_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_b_1590_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_tail_1594_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(lean_object* v_a_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = 0;
return v___x_1609_;
}
else
{
lean_object* v_key_1610_; lean_object* v_tail_1611_; uint8_t v___x_1612_; 
v_key_1610_ = lean_ctor_get(v_x_1608_, 0);
v_tail_1611_ = lean_ctor_get(v_x_1608_, 2);
v___x_1612_ = lean_nat_dec_eq(v_key_1610_, v_a_1607_);
if (v___x_1612_ == 0)
{
v_x_1608_ = v_tail_1611_;
goto _start;
}
else
{
return v___x_1612_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1607_ = stack[0].m_obj;
lean_object* v_x_1608_ = stack[1].m_obj;
uint8_t v_res_1614_;
v_res_1614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1607_, v_x_1608_);
stack->m_num = v_res_1614_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg___boxed(lean_object* v_a_1615_, lean_object* v_x_1616_){
_start:
{
uint8_t v_res_1617_; lean_object* v_r_1618_; 
v_res_1617_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1615_, v_x_1616_);
lean_dec(v_x_1616_);
lean_dec(v_a_1615_);
v_r_1618_ = lean_box(v_res_1617_);
return v_r_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
return v_x_1619_;
}
else
{
lean_object* v_key_1621_; lean_object* v_value_1622_; lean_object* v_tail_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1646_; 
v_key_1621_ = lean_ctor_get(v_x_1620_, 0);
v_value_1622_ = lean_ctor_get(v_x_1620_, 1);
v_tail_1623_ = lean_ctor_get(v_x_1620_, 2);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1625_ = v_x_1620_;
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_tail_1623_);
lean_inc(v_value_1622_);
lean_inc(v_key_1621_);
lean_dec(v_x_1620_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1646_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; uint64_t v___x_1628_; uint64_t v___x_1629_; uint64_t v___x_1630_; uint64_t v_fold_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; uint64_t v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; size_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1627_ = lean_array_get_size(v_x_1619_);
v___x_1628_ = lean_uint64_of_nat(v_key_1621_);
v___x_1629_ = 32ULL;
v___x_1630_ = lean_uint64_shift_right(v___x_1628_, v___x_1629_);
v_fold_1631_ = lean_uint64_xor(v___x_1628_, v___x_1630_);
v___x_1632_ = 16ULL;
v___x_1633_ = lean_uint64_shift_right(v_fold_1631_, v___x_1632_);
v___x_1634_ = lean_uint64_xor(v_fold_1631_, v___x_1633_);
v___x_1635_ = lean_uint64_to_usize(v___x_1634_);
v___x_1636_ = lean_usize_of_nat(v___x_1627_);
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_sub(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_usize_land(v___x_1635_, v___x_1638_);
v___x_1640_ = lean_array_uget_borrowed(v_x_1619_, v___x_1639_);
lean_inc(v___x_1640_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 2, v___x_1640_);
v___x_1642_ = v___x_1625_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_key_1621_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_value_1622_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_array_uset(v_x_1619_, v___x_1639_, v___x_1642_);
v_x_1619_ = v___x_1643_;
v_x_1620_ = v_tail_1623_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(lean_object* v_i_1647_, lean_object* v_source_1648_, lean_object* v_target_1649_){
_start:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_array_get_size(v_source_1648_);
v___x_1651_ = lean_nat_dec_lt(v_i_1647_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec_ref(v_source_1648_);
lean_dec(v_i_1647_);
return v_target_1649_;
}
else
{
lean_object* v_es_1652_; lean_object* v___x_1653_; lean_object* v_source_1654_; lean_object* v_target_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_es_1652_ = lean_array_fget(v_source_1648_, v_i_1647_);
v___x_1653_ = lean_box(0);
v_source_1654_ = lean_array_fset(v_source_1648_, v_i_1647_, v___x_1653_);
v_target_1655_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_target_1649_, v_es_1652_);
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_nat_add(v_i_1647_, v___x_1656_);
lean_dec(v_i_1647_);
v_i_1647_ = v___x_1657_;
v_source_1648_ = v_source_1654_;
v_target_1649_ = v_target_1655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(lean_object* v_data_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_nbuckets_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1660_ = lean_array_get_size(v_data_1659_);
v___x_1661_ = lean_unsigned_to_nat(2u);
v_nbuckets_1662_ = lean_nat_mul(v___x_1660_, v___x_1661_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_mk_array(v_nbuckets_1662_, v___x_1664_);
v___x_1666_ = lean_array_propagate_mark(v_data_1659_, v___x_1665_);
v___x_1667_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v___x_1663_, v_data_1659_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(lean_object* v_m_1668_, lean_object* v_a_1669_, lean_object* v_b_1670_){
_start:
{
lean_object* v_size_1671_; lean_object* v_buckets_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1715_; 
v_size_1671_ = lean_ctor_get(v_m_1668_, 0);
v_buckets_1672_ = lean_ctor_get(v_m_1668_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_m_1668_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1674_ = v_m_1668_;
v_isShared_1675_ = v_isSharedCheck_1715_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_buckets_1672_);
lean_inc(v_size_1671_);
lean_dec(v_m_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1715_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; uint64_t v_fold_1680_; uint64_t v___x_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v_bkt_1689_; uint8_t v___x_1690_; 
v___x_1676_ = lean_array_get_size(v_buckets_1672_);
v___x_1677_ = lean_uint64_of_nat(v_a_1669_);
v___x_1678_ = 32ULL;
v___x_1679_ = lean_uint64_shift_right(v___x_1677_, v___x_1678_);
v_fold_1680_ = lean_uint64_xor(v___x_1677_, v___x_1679_);
v___x_1681_ = 16ULL;
v___x_1682_ = lean_uint64_shift_right(v_fold_1680_, v___x_1681_);
v___x_1683_ = lean_uint64_xor(v_fold_1680_, v___x_1682_);
v___x_1684_ = lean_uint64_to_usize(v___x_1683_);
v___x_1685_ = lean_usize_of_nat(v___x_1676_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_sub(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_usize_land(v___x_1684_, v___x_1687_);
v_bkt_1689_ = lean_array_uget_borrowed(v_buckets_1672_, v___x_1688_);
v___x_1690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1669_, v_bkt_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v_size_x27_1692_; lean_object* v___x_1693_; lean_object* v_buckets_x27_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1691_ = lean_unsigned_to_nat(1u);
v_size_x27_1692_ = lean_nat_add(v_size_1671_, v___x_1691_);
lean_dec(v_size_1671_);
lean_inc(v_bkt_1689_);
v___x_1693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1693_, 0, v_a_1669_);
lean_ctor_set(v___x_1693_, 1, v_b_1670_);
lean_ctor_set(v___x_1693_, 2, v_bkt_1689_);
v_buckets_x27_1694_ = lean_array_uset(v_buckets_1672_, v___x_1688_, v___x_1693_);
v___x_1695_ = lean_unsigned_to_nat(4u);
v___x_1696_ = lean_nat_mul(v_size_x27_1692_, v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(3u);
v___x_1698_ = lean_nat_div(v___x_1696_, v___x_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_array_get_size(v_buckets_x27_1694_);
v___x_1700_ = lean_nat_dec_le(v___x_1698_, v___x_1699_);
lean_dec(v___x_1698_);
if (v___x_1700_ == 0)
{
lean_object* v_val_1701_; lean_object* v___x_1703_; 
v_val_1701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_buckets_x27_1694_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_val_1701_);
lean_ctor_set(v___x_1674_, 0, v_size_x27_1692_);
v___x_1703_ = v___x_1674_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_size_x27_1692_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_val_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1706_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_buckets_x27_1694_);
lean_ctor_set(v___x_1674_, 0, v_size_x27_1692_);
v___x_1706_ = v___x_1674_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_size_x27_1692_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_buckets_x27_1694_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v___x_1708_; lean_object* v_buckets_x27_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_inc(v_bkt_1689_);
v___x_1708_ = lean_box(0);
v_buckets_x27_1709_ = lean_array_uset(v_buckets_1672_, v___x_1688_, v___x_1708_);
v___x_1710_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1669_, v_b_1670_, v_bkt_1689_);
v___x_1711_ = lean_array_uset(v_buckets_x27_1709_, v___x_1688_, v___x_1710_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1711_);
v___x_1713_ = v___x_1674_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_size_1671_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__2));
v___x_1720_ = lean_unsigned_to_nat(48u);
v___x_1721_ = lean_unsigned_to_nat(239u);
v___x_1722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__1));
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__0));
v___x_1724_ = l_mkPanicMessageWithDecl(v___x_1723_, v___x_1722_, v___x_1721_, v___x_1720_, v___x_1719_);
return v___x_1724_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(lean_object* v_as_1725_, size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_a_1742_; uint8_t v___x_1746_; 
v___x_1746_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_b_1728_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v_snd_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1786_; 
v_a_1748_ = lean_array_uget_borrowed(v_as_1725_, v_i_1727_);
v_snd_1749_ = lean_ctor_get(v_a_1748_, 1);
v_fst_1750_ = lean_ctor_get(v_a_1748_, 0);
v_snd_1751_ = lean_ctor_get(v_snd_1749_, 1);
v_fst_1752_ = lean_ctor_get(v_b_1728_, 0);
v_snd_1753_ = lean_ctor_get(v_b_1728_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_b_1728_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1755_ = v_b_1728_;
v_isShared_1756_ = v_isSharedCheck_1786_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_inc(v_fst_1752_);
lean_dec(v_b_1728_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1786_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_fst_1750_, v___y_1730_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
if (lean_obj_tag(v_a_1758_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v_val_1759_ = lean_ctor_get(v_a_1758_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v_a_1758_, 1);
lean_inc_n(v_snd_1751_, 2);
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_snd_1753_, v_val_1759_, v_snd_1751_);
lean_inc(v_fst_1750_);
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_fst_1752_, v_fst_1750_, v_snd_1751_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1760_);
lean_ctor_set(v___x_1755_, 0, v___x_1761_);
v___x_1763_ = v___x_1755_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1760_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
v_a_1742_ = v___x_1763_;
goto v___jp_1741_;
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v_a_1758_);
v___x_1765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___closed__3);
v___x_1766_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__2(v___x_1765_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1766_, 1);
if (v_isShared_1756_ == 0)
{
v___x_1768_ = v___x_1755_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fst_1752_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_snd_1753_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
v_a_1742_ = v___x_1768_;
goto v___jp_1741_;
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
v_a_1770_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1766_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
v_a_1778_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1757_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1757_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
v___jp_1741_:
{
size_t v___x_1743_; size_t v___x_1744_; 
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1727_, v___x_1743_);
v_i_1727_ = v___x_1744_;
v_b_1728_ = v_a_1742_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1725_ = stack[0].m_obj;
size_t v_sz_1726_ = stack[1].m_num;
size_t v_i_1727_ = stack[2].m_num;
lean_object* v_b_1728_ = stack[3].m_obj;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v___y_1730_ = stack[5].m_obj;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v___y_1732_ = stack[7].m_obj;
lean_object* v___y_1733_ = stack[8].m_obj;
lean_object* v___y_1734_ = stack[9].m_obj;
lean_object* v___y_1735_ = stack[10].m_obj;
lean_object* v___y_1736_ = stack[11].m_obj;
lean_object* v___y_1737_ = stack[12].m_obj;
lean_object* v___y_1738_ = stack[13].m_obj;
lean_object* v___y_1739_ = stack[14].m_obj;
lean_object* v_res_1787_;
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_as_1725_, v_sz_1726_, v_i_1727_, v_b_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3___boxed(lean_object* v_as_1788_, lean_object* v_sz_1789_, lean_object* v_i_1790_, lean_object* v_b_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
size_t v_sz_boxed_1804_; size_t v_i_boxed_1805_; lean_object* v_res_1806_; 
v_sz_boxed_1804_ = lean_unbox_usize(v_sz_1789_);
lean_dec(v_sz_1789_);
v_i_boxed_1805_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_as_1788_, v_sz_boxed_1804_, v_i_boxed_1805_, v_b_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_as_1788_);
return v_res_1806_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object* v_arr_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_exprCex_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_atomCex_1830_; lean_object* v___x_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_box(0);
v_exprCex_1822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new___closed__1);
v___x_1823_ = lean_array_get_size(v_arr_1807_);
v___x_1824_ = lean_unsigned_to_nat(4u);
v___x_1825_ = lean_nat_mul(v___x_1823_, v___x_1824_);
v___x_1826_ = lean_unsigned_to_nat(3u);
v___x_1827_ = lean_nat_div(v___x_1825_, v___x_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = l_Nat_nextPowerOfTwo(v___x_1827_);
lean_dec(v___x_1827_);
v___x_1829_ = lean_mk_array(v___x_1828_, v___x_1821_);
v_atomCex_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_atomCex_1830_, 0, v___x_1820_);
lean_ctor_set(v_atomCex_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_exprCex_1822_);
lean_ctor_set(v___x_1831_, 1, v_atomCex_1830_);
v_sz_1832_ = lean_array_size(v_arr_1807_);
v___x_1833_ = ((size_t)0ULL);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__3(v_arr_1807_, v_sz_1832_, v___x_1833_, v___x_1831_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1851_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1851_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1850_; 
v_fst_1839_ = lean_ctor_get(v_a_1835_, 0);
v_snd_1840_ = lean_ctor_get(v_a_1835_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1842_ = v_a_1835_;
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_snd_1840_);
lean_inc(v_fst_1839_);
lean_dec(v_a_1835_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_fst_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_snd_1840_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1845_);
v___x_1847_ = v___x_1837_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1834_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1834_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_0interp(lean_interpreter_value* stack)
{
lean_object* v_arr_1807_ = stack[0].m_obj;
lean_object* v_a_1808_ = stack[1].m_obj;
lean_object* v_a_1809_ = stack[2].m_obj;
lean_object* v_a_1810_ = stack[3].m_obj;
lean_object* v_a_1811_ = stack[4].m_obj;
lean_object* v_a_1812_ = stack[5].m_obj;
lean_object* v_a_1813_ = stack[6].m_obj;
lean_object* v_a_1814_ = stack[7].m_obj;
lean_object* v_a_1815_ = stack[8].m_obj;
lean_object* v_a_1816_ = stack[9].m_obj;
lean_object* v_a_1817_ = stack[10].m_obj;
lean_object* v_a_1818_ = stack[11].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_arr_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray___boxed(lean_object* v_arr_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_arr_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec_ref(v_arr_1861_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0(lean_object* v_00_u03b2_1875_, lean_object* v_m_1876_, lean_object* v_a_1877_, lean_object* v_b_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0___redArg(v_m_1876_, v_a_1877_, v_b_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1(lean_object* v_00_u03b2_1880_, lean_object* v_m_1881_, lean_object* v_a_1882_, lean_object* v_b_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1___redArg(v_m_1881_, v_a_1882_, v_b_1883_);
return v___x_1884_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_object* v_00_u03b2_1885_, lean_object* v_a_1886_, lean_object* v_x_1887_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___redArg(v_a_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1886_ = stack[1].m_obj;
lean_object* v_x_1887_ = stack[2].m_obj;
uint8_t v_res_1889_;
v_res_1889_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(lean_box(0), v_a_1886_, v_x_1887_);
stack->m_num = v_res_1889_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1890_, lean_object* v_a_1891_, lean_object* v_x_1892_){
_start:
{
uint8_t v_res_1893_; lean_object* v_r_1894_; 
v_res_1893_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__0(v_00_u03b2_1890_, v_a_1891_, v_x_1892_);
lean_dec(v_x_1892_);
lean_dec(v_a_1891_);
v_r_1894_ = lean_box(v_res_1893_);
return v_r_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1(lean_object* v_00_u03b2_1895_, lean_object* v_data_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1___redArg(v_data_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2(lean_object* v_00_u03b2_1898_, lean_object* v_a_1899_, lean_object* v_b_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__2___redArg(v_a_1899_, v_b_1900_, v_x_1901_);
return v___x_1902_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_object* v_00_u03b2_1903_, lean_object* v_a_1904_, lean_object* v_x_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___redArg(v_a_1904_, v_x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1904_ = stack[1].m_obj;
lean_object* v_x_1905_ = stack[2].m_obj;
uint8_t v_res_1907_;
v_res_1907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(lean_box(0), v_a_1904_, v_x_1905_);
stack->m_num = v_res_1907_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1908_, lean_object* v_a_1909_, lean_object* v_x_1910_){
_start:
{
uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_res_1911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__4(v_00_u03b2_1908_, v_a_1909_, v_x_1910_);
lean_dec(v_x_1910_);
lean_dec_ref(v_a_1909_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5(lean_object* v_00_u03b2_1913_, lean_object* v_data_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5___redArg(v_data_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6(lean_object* v_00_u03b2_1916_, lean_object* v_a_1917_, lean_object* v_b_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__6___redArg(v_a_1917_, v_b_1918_, v_x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1921_, lean_object* v_i_1922_, lean_object* v_source_1923_, lean_object* v_target_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3___redArg(v_i_1922_, v_source_1923_, v_target_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8(lean_object* v_00_u03b2_1926_, lean_object* v_i_1927_, lean_object* v_source_1928_, lean_object* v_target_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8___redArg(v_i_1927_, v_source_1928_, v_target_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1932_, v_x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray_spec__1_spec__5_spec__8_spec__11___redArg(v_x_1936_, v_x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object* v_cert_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_CegarM_drainNewHyps___redArg___closed__0));
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_cert_1943_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
return v___x_1946_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object* v_cert_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v_usedHyps_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1950_ = lean_st_ref_get(v_a_1948_);
v_usedHyps_1951_ = lean_ctor_get(v___x_1950_, 2);
lean_inc_ref(v_usedHyps_1951_);
lean_dec(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_usedHyps_1951_);
lean_ctor_set(v___x_1952_, 1, v_cert_1947_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cert_1947_ = stack[0].m_obj;
lean_object* v_a_1948_ = stack[1].m_obj;
lean_object* v_res_1954_;
v_res_1954_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1947_, v_a_1948_);
stack->m_obj
 = v_res_1954_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg___boxed(lean_object* v_cert_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1955_, v_a_1956_);
lean_dec(v_a_1956_);
return v_res_1958_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(lean_object* v_cert_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v_cert_1959_, v_a_1961_);
return v___x_1975_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_CegarM_createCert_0interp(lean_interpreter_value* stack)
{
lean_object* v_cert_1959_ = stack[0].m_obj;
lean_object* v_a_1960_ = stack[1].m_obj;
lean_object* v_a_1961_ = stack[2].m_obj;
lean_object* v_a_1962_ = stack[3].m_obj;
lean_object* v_a_1963_ = stack[4].m_obj;
lean_object* v_a_1964_ = stack[5].m_obj;
lean_object* v_a_1965_ = stack[6].m_obj;
lean_object* v_a_1966_ = stack[7].m_obj;
lean_object* v_a_1967_ = stack[8].m_obj;
lean_object* v_a_1968_ = stack[9].m_obj;
lean_object* v_a_1969_ = stack[10].m_obj;
lean_object* v_a_1970_ = stack[11].m_obj;
lean_object* v_a_1971_ = stack[12].m_obj;
lean_object* v_a_1972_ = stack[13].m_obj;
lean_object* v_a_1973_ = stack[14].m_obj;
lean_object* v_res_1976_;
v_res_1976_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(v_cert_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
stack->m_obj
 = v_res_1976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___boxed(lean_object* v_cert_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert(v_cert_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1993_;
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
