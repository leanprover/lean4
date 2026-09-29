// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types public import Lean.Meta.Sym.Arith.Functions public import Lean.Meta.Sym.Arith.MonadVar import Lean.Meta.Sym.Arith.Poly
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ring polynomial degree "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = " exceeds threshold `(ringMaxDegree := "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`grind` internal error, ring does not have a characteristic"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v___x_5_, 1);
v___x_7_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_19_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_19_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v_ringSteps_12_; lean_object* v_steps_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_ringSteps_12_ = lean_ctor_get(v_a_8_, 6);
lean_inc(v_ringSteps_12_);
lean_dec(v_a_8_);
v_steps_13_ = lean_ctor_get(v_a_6_, 8);
lean_inc(v_steps_13_);
lean_dec(v_a_6_);
v___x_14_ = lean_nat_dec_le(v_ringSteps_12_, v_steps_13_);
lean_dec(v_steps_13_);
lean_dec(v_ringSteps_12_);
v___x_15_ = lean_box(v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_a_6_);
v_a_20_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_7_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_7_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_5_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_5_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_41_, v_a_43_, v_a_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec(v_a_53_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t v___x_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_rings_67_; lean_object* v_exprToRingId_68_; lean_object* v_semirings_69_; lean_object* v_exprToSemiringId_70_; lean_object* v_ncRings_71_; lean_object* v_exprToNCRingId_72_; lean_object* v_ncSemirings_73_; lean_object* v_exprToNCSemiringId_74_; lean_object* v_steps_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_rings_67_ = lean_ctor_get(v_s_66_, 0);
v_exprToRingId_68_ = lean_ctor_get(v_s_66_, 1);
v_semirings_69_ = lean_ctor_get(v_s_66_, 2);
v_exprToSemiringId_70_ = lean_ctor_get(v_s_66_, 3);
v_ncRings_71_ = lean_ctor_get(v_s_66_, 4);
v_exprToNCRingId_72_ = lean_ctor_get(v_s_66_, 5);
v_ncSemirings_73_ = lean_ctor_get(v_s_66_, 6);
v_exprToNCSemiringId_74_ = lean_ctor_get(v_s_66_, 7);
v_steps_75_ = lean_ctor_get(v_s_66_, 8);
v_isSharedCheck_82_ = !lean_is_exclusive(v_s_66_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v_s_66_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_steps_75_);
lean_inc(v_exprToNCSemiringId_74_);
lean_inc(v_ncSemirings_73_);
lean_inc(v_exprToNCRingId_72_);
lean_inc(v_ncRings_71_);
lean_inc(v_exprToSemiringId_70_);
lean_inc(v_semirings_69_);
lean_inc(v_exprToRingId_68_);
lean_inc(v_rings_67_);
lean_dec(v_s_66_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_rings_67_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_exprToRingId_68_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_semirings_69_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_exprToSemiringId_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_ncRings_71_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v_exprToNCRingId_72_);
lean_ctor_set(v_reuseFailAlloc_81_, 6, v_ncSemirings_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 7, v_exprToNCSemiringId_74_);
lean_ctor_set(v_reuseFailAlloc_81_, 8, v_steps_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*9, v___x_65_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_s_84_){
_start:
{
uint8_t v___x_5932__boxed_85_; lean_object* v_res_86_; 
v___x_5932__boxed_85_ = lean_unbox(v___x_83_);
v_res_86_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_5932__boxed_85_, v_s_84_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0));
v___x_89_ = l_Lean_stringToMessageData(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2));
v___x_92_ = l_Lean_stringToMessageData(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4));
v___x_95_ = l_Lean_stringToMessageData(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object* v_p_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_98_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_196_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_196_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_196_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_196_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_ringMaxDegree_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_ringMaxDegree_111_ = lean_ctor_get(v_a_107_, 7);
lean_inc(v_ringMaxDegree_111_);
lean_dec(v_a_107_);
v___x_112_ = l_Lean_Grind_CommRing_Poly_degree(v_p_96_);
v___x_113_ = lean_nat_dec_le(v_ringMaxDegree_111_, v___x_112_);
lean_dec(v_ringMaxDegree_111_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v___x_112_);
v___x_114_ = lean_box(v___x_113_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v___x_120_; 
lean_del_object(v___x_109_);
v___x_118_ = lean_box(v___x_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v___x_118_);
v___x_120_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_97_, v_a_103_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_187_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_187_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
uint8_t v_reportedMaxDegreeIssue_125_; 
v_reportedMaxDegreeIssue_125_ = lean_ctor_get_uint8(v_a_121_, sizeof(void*)*9);
lean_dec(v_a_121_);
if (v_reportedMaxDegreeIssue_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_del_object(v___x_123_);
v___x_126_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_127_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_126_, v___f_119_, v_a_97_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref_known(v___x_127_, 1);
v___x_128_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
v___x_129_ = l_Nat_reprFast(v___x_112_);
v___x_130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = l_Lean_MessageData_ofFormat(v___x_130_);
lean_inc_ref(v___x_131_);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_128_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_131_);
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_99_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_166_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_166_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_166_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_166_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
uint8_t v_verbose_143_; 
v_verbose_143_ = lean_ctor_get_uint8(v_a_139_, 0);
lean_dec(v_a_139_);
if (v_verbose_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec_ref_known(v___x_137_, 2);
v___x_144_ = lean_box(v___x_113_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v___x_148_; 
lean_del_object(v___x_141_);
v___x_148_ = l_Lean_Meta_Sym_reportIssue(v___x_137_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_156_; 
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_157_);
v___x_150_ = v___x_148_;
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
else
{
lean_dec(v___x_148_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_156_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_box(v___x_113_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_148_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_148_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref_known(v___x_137_, 2);
v_a_167_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_138_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_138_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v___x_112_);
v_a_175_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_127_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_127_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_185_; 
lean_dec_ref(v___f_119_);
lean_dec(v___x_112_);
v___x_183_ = lean_box(v___x_113_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_183_);
v___x_185_ = v___x_123_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v___f_119_);
lean_dec(v___x_112_);
v_a_188_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_120_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_120_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_106_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_106_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object* v_p_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_p_205_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object* v_p_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_216_, v_a_217_, v_a_219_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object* v_p_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_p_229_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_rings_244_; lean_object* v_exprToRingId_245_; lean_object* v_semirings_246_; lean_object* v_exprToSemiringId_247_; lean_object* v_ncRings_248_; lean_object* v_exprToNCRingId_249_; lean_object* v_ncSemirings_250_; lean_object* v_exprToNCSemiringId_251_; lean_object* v_steps_252_; uint8_t v_reportedMaxDegreeIssue_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_rings_244_ = lean_ctor_get(v_s_243_, 0);
v_exprToRingId_245_ = lean_ctor_get(v_s_243_, 1);
v_semirings_246_ = lean_ctor_get(v_s_243_, 2);
v_exprToSemiringId_247_ = lean_ctor_get(v_s_243_, 3);
v_ncRings_248_ = lean_ctor_get(v_s_243_, 4);
v_exprToNCRingId_249_ = lean_ctor_get(v_s_243_, 5);
v_ncSemirings_250_ = lean_ctor_get(v_s_243_, 6);
v_exprToNCSemiringId_251_ = lean_ctor_get(v_s_243_, 7);
v_steps_252_ = lean_ctor_get(v_s_243_, 8);
v_reportedMaxDegreeIssue_253_ = lean_ctor_get_uint8(v_s_243_, sizeof(void*)*9);
v_isSharedCheck_261_ = !lean_is_exclusive(v_s_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_s_243_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_steps_252_);
lean_inc(v_exprToNCSemiringId_251_);
lean_inc(v_ncSemirings_250_);
lean_inc(v_exprToNCRingId_249_);
lean_inc(v_ncRings_248_);
lean_inc(v_exprToSemiringId_247_);
lean_inc(v_semirings_246_);
lean_inc(v_exprToRingId_245_);
lean_inc(v_rings_244_);
lean_dec(v_s_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_nat_add(v_steps_252_, v_n_242_);
lean_dec(v_steps_252_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 8, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_rings_244_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_exprToRingId_245_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_semirings_246_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_exprToSemiringId_247_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_ncRings_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 5, v_exprToNCRingId_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 6, v_ncSemirings_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 7, v_exprToNCSemiringId_251_);
lean_ctor_set(v_reuseFailAlloc_260_, 8, v___x_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_260_, sizeof(void*)*9, v_reportedMaxDegreeIssue_253_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_262_, v_s_263_);
lean_dec(v_n_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_268_, 0, v_n_265_);
v___x_269_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_270_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_269_, v___f_268_, v_a_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_271_, v_a_272_);
lean_dec(v_a_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_275_, v_a_276_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec(v_a_289_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_301_, lean_object* v_x_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = 0;
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_316_, 0, v_ringId_301_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*2, v___x_314_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
lean_inc_ref(v_a_309_);
lean_inc(v_a_308_);
lean_inc_ref(v_a_307_);
lean_inc(v_a_306_);
lean_inc_ref(v_a_305_);
lean_inc(v_a_304_);
lean_inc(v_a_303_);
v___x_317_ = lean_apply_12(v_x_302_, v___x_316_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_318_, lean_object* v_x_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_318_, v_x_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec(v_a_320_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_332_, lean_object* v_ringId_333_, lean_object* v_x_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = 0;
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_348_, 0, v_ringId_333_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*2, v___x_346_);
lean_inc(v_a_344_);
lean_inc_ref(v_a_343_);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_337_);
lean_inc(v_a_336_);
lean_inc(v_a_335_);
v___x_349_ = lean_apply_12(v_x_334_, v___x_348_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, lean_box(0));
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_350_, lean_object* v_ringId_351_, lean_object* v_x_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_350_, v_ringId_351_, v_x_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec(v_a_353_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_365_){
_start:
{
lean_object* v_ringId_367_; lean_object* v___x_368_; 
v_ringId_367_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_ringId_367_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_ringId_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_369_);
lean_dec_ref(v_a_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_ringId_384_; lean_object* v___x_385_; 
v_ringId_384_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_ringId_384_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_ringId_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Sym_canon(v_e_399_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = l_Lean_Meta_Sym_shareCommon(v_a_413_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_414_;
}
else
{
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_429_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v_env_470_; lean_object* v___x_471_; lean_object* v_toCold_472_; lean_object* v_mctx_473_; lean_object* v_lctx_474_; lean_object* v_options_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_469_ = lean_st_ref_get(v___y_467_);
v_env_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_469_);
v___x_471_ = lean_st_ref_get(v___y_465_);
v_toCold_472_ = lean_ctor_get(v___y_466_, 0);
v_mctx_473_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_mctx_473_);
lean_dec(v___x_471_);
v_lctx_474_ = lean_ctor_get(v___y_464_, 2);
v_options_475_ = lean_ctor_get(v_toCold_472_, 2);
lean_inc_ref(v_options_475_);
lean_inc_ref(v_lctx_474_);
v___x_476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_476_, 0, v_env_470_);
lean_ctor_set(v___x_476_, 1, v_mctx_473_);
lean_ctor_set(v___x_476_, 2, v_lctx_474_);
lean_ctor_set(v___x_476_, 3, v_options_475_);
v___x_477_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_msgData_463_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_ref_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v_ref_492_ = lean_ctor_get(v___y_489_, 2);
v___x_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc(v_ref_492_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_ref_492_);
lean_ctor_set(v___x_498_, 1, v_a_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_519_, v_a_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_540_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_540_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_540_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_ringId_530_; lean_object* v_rings_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_ringId_530_ = lean_ctor_get(v_a_513_, 0);
v_rings_531_ = lean_ctor_get(v_a_526_, 1);
lean_inc_ref(v_rings_531_);
lean_dec(v_a_526_);
v___x_532_ = lean_array_get_size(v_rings_531_);
v___x_533_ = lean_nat_dec_lt(v_ringId_530_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v_rings_531_);
lean_del_object(v___x_528_);
v___x_534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_535_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_534_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_fget(v_rings_531_, v_ringId_530_);
lean_dec_ref(v_rings_531_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_536_);
v___x_538_ = v___x_528_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_525_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_525_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_562_, lean_object* v_msg_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_563_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_577_, v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_592_, lean_object* v_f_593_, lean_object* v_s_594_){
_start:
{
lean_object* v_exp_595_; lean_object* v_rings_596_; lean_object* v_semirings_597_; lean_object* v_ncRings_598_; lean_object* v_ncSemirings_599_; lean_object* v_typeClassify_600_; lean_object* v_orders_601_; lean_object* v_typeOrderClassify_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_exp_595_ = lean_ctor_get(v_s_594_, 0);
v_rings_596_ = lean_ctor_get(v_s_594_, 1);
v_semirings_597_ = lean_ctor_get(v_s_594_, 2);
v_ncRings_598_ = lean_ctor_get(v_s_594_, 3);
v_ncSemirings_599_ = lean_ctor_get(v_s_594_, 4);
v_typeClassify_600_ = lean_ctor_get(v_s_594_, 5);
v_orders_601_ = lean_ctor_get(v_s_594_, 6);
v_typeOrderClassify_602_ = lean_ctor_get(v_s_594_, 7);
v___x_603_ = lean_array_get_size(v_rings_596_);
v___x_604_ = lean_nat_dec_lt(v_ringId_592_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_f_593_);
return v_s_594_;
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
lean_inc_ref(v_typeOrderClassify_602_);
lean_inc_ref(v_orders_601_);
lean_inc_ref(v_typeClassify_600_);
lean_inc_ref(v_ncSemirings_599_);
lean_inc_ref(v_ncRings_598_);
lean_inc_ref(v_semirings_597_);
lean_inc_ref(v_rings_596_);
lean_inc(v_exp_595_);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_594_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_617_ = lean_ctor_get(v_s_594_, 7);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_s_594_, 6);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_s_594_, 5);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_s_594_, 4);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_s_594_, 3);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_s_594_, 2);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_s_594_, 1);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_s_594_, 0);
lean_dec(v_unused_624_);
v___x_606_ = v_s_594_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_s_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_v_608_ = lean_array_fget(v_rings_596_, v_ringId_592_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v_rings_596_, v_ringId_592_, v___x_609_);
v___x_611_ = lean_apply_1(v_f_593_, v_v_608_);
v___x_612_ = lean_array_fset(v_xs_x27_610_, v_ringId_592_, v___x_611_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_612_);
v___x_614_ = v___x_606_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_exp_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_semirings_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_ncRings_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_ncSemirings_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_typeClassify_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_orders_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_typeOrderClassify_602_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_625_, lean_object* v_f_626_, lean_object* v_s_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_625_, v_f_626_, v_s_627_);
lean_dec(v_ringId_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_ringId_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_ringId_633_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_ringId_633_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_634_, 0, v_ringId_633_);
lean_closure_set(v___f_634_, 1, v_f_629_);
v___x_635_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_636_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_635_, v___f_634_, v_a_631_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_642_, v_a_643_, v_a_649_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_669_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_689_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_689_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_689_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_ringId_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v_ringId_684_ = lean_ctor_get(v_a_675_, 0);
v___x_685_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_a_680_, v_ringId_684_);
lean_dec(v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_679_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_679_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_698_, v_a_699_, v_a_700_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_703_, v_a_704_, v_a_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
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
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object* v_ringId_729_, lean_object* v_f_730_, lean_object* v_s_731_){
_start:
{
lean_object* v_rings_732_; lean_object* v_exprToRingId_733_; lean_object* v_semirings_734_; lean_object* v_exprToSemiringId_735_; lean_object* v_ncRings_736_; lean_object* v_exprToNCRingId_737_; lean_object* v_ncSemirings_738_; lean_object* v_exprToNCSemiringId_739_; lean_object* v_steps_740_; uint8_t v_reportedMaxDegreeIssue_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_762_; 
v_rings_732_ = lean_ctor_get(v_s_731_, 0);
v_exprToRingId_733_ = lean_ctor_get(v_s_731_, 1);
v_semirings_734_ = lean_ctor_get(v_s_731_, 2);
v_exprToSemiringId_735_ = lean_ctor_get(v_s_731_, 3);
v_ncRings_736_ = lean_ctor_get(v_s_731_, 4);
v_exprToNCRingId_737_ = lean_ctor_get(v_s_731_, 5);
v_ncSemirings_738_ = lean_ctor_get(v_s_731_, 6);
v_exprToNCSemiringId_739_ = lean_ctor_get(v_s_731_, 7);
v_steps_740_ = lean_ctor_get(v_s_731_, 8);
v_reportedMaxDegreeIssue_741_ = lean_ctor_get_uint8(v_s_731_, sizeof(void*)*9);
v_isSharedCheck_762_ = !lean_is_exclusive(v_s_731_);
if (v_isSharedCheck_762_ == 0)
{
v___x_743_ = v_s_731_;
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_steps_740_);
lean_inc(v_exprToNCSemiringId_739_);
lean_inc(v_ncSemirings_738_);
lean_inc(v_exprToNCRingId_737_);
lean_inc(v_ncRings_736_);
lean_inc(v_exprToSemiringId_735_);
lean_inc(v_semirings_734_);
lean_inc(v_exprToRingId_733_);
lean_inc(v_rings_732_);
lean_dec(v_s_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_ringId_729_, v___x_745_);
v___x_747_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_748_ = l_Array_rightpad___redArg(v___x_746_, v___x_747_, v_rings_732_);
lean_dec(v___x_746_);
v___x_749_ = lean_array_get_size(v___x_748_);
v___x_750_ = lean_nat_dec_lt(v_ringId_729_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_f_730_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_748_);
v___x_752_ = v___x_743_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_exprToRingId_733_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_semirings_734_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_exprToSemiringId_735_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_ncRings_736_);
lean_ctor_set(v_reuseFailAlloc_753_, 5, v_exprToNCRingId_737_);
lean_ctor_set(v_reuseFailAlloc_753_, 6, v_ncSemirings_738_);
lean_ctor_set(v_reuseFailAlloc_753_, 7, v_exprToNCSemiringId_739_);
lean_ctor_set(v_reuseFailAlloc_753_, 8, v_steps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*9, v_reportedMaxDegreeIssue_741_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v_v_754_; lean_object* v___x_755_; lean_object* v_xs_x27_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v_v_754_ = lean_array_fget(v___x_748_, v_ringId_729_);
v___x_755_ = lean_box(0);
v_xs_x27_756_ = lean_array_fset(v___x_748_, v_ringId_729_, v___x_755_);
v___x_757_ = lean_apply_1(v_f_730_, v_v_754_);
v___x_758_ = lean_array_fset(v_xs_x27_756_, v_ringId_729_, v___x_757_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_758_);
v___x_760_ = v___x_743_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_exprToRingId_733_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_semirings_734_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_exprToSemiringId_735_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_ncRings_736_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v_exprToNCRingId_737_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_ncSemirings_738_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_exprToNCSemiringId_739_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_steps_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_761_, sizeof(void*)*9, v_reportedMaxDegreeIssue_741_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object* v_ringId_763_, lean_object* v_f_764_, lean_object* v_s_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(v_ringId_763_, v_f_764_, v_s_765_);
lean_dec(v_ringId_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object* v_f_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_ringId_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_ringId_771_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_ringId_771_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_772_, 0, v_ringId_771_);
lean_closure_set(v___f_772_, 1, v_f_767_);
v___x_773_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_773_, v___f_772_, v_a_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object* v_f_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object* v_f_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_780_, v_a_781_, v_a_782_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object* v_f_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(v_f_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0));
v___x_810_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed), 12, 0);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object* v___x_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_815_, v___y_816_, v___y_824_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_844_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_844_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_844_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_toRingState_832_; lean_object* v_vars_833_; lean_object* v_size_834_; uint8_t v___x_835_; 
v_toRingState_832_ = lean_ctor_get(v_a_828_, 0);
lean_inc_ref(v_toRingState_832_);
lean_dec(v_a_828_);
v_vars_833_ = lean_ctor_get(v_toRingState_832_, 0);
lean_inc_ref(v_vars_833_);
lean_dec_ref(v_toRingState_832_);
v_size_834_ = lean_ctor_get(v_vars_833_, 2);
v___x_835_ = lean_nat_dec_lt(v_x_814_, v_size_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec_ref(v_vars_833_);
v___x_836_ = l_outOfBounds___redArg(v___x_813_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_836_);
v___x_838_ = v___x_830_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_PersistentArray_get_x21___redArg(v___x_813_, v_vars_833_, v_x_814_);
lean_dec_ref(v_vars_833_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_840_);
v___x_842_ = v___x_830_;
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
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_827_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_827_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object* v___x_853_, lean_object* v_x_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(v___x_853_, v_x_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v_x_854_);
lean_dec_ref(v___x_853_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0(void){
_start:
{
lean_object* v___x_868_; lean_object* v___f_869_; 
v___x_868_ = l_Lean_instInhabitedExpr;
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_869_, 0, v___x_868_);
return v___f_869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM(void){
_start:
{
lean_object* v___f_870_; 
v___f_870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0);
return v___f_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_ringId_884_; lean_object* v_gen_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_ringId_884_ = lean_ctor_get(v_a_872_, 0);
v_gen_885_ = lean_ctor_get(v_a_872_, 1);
v___x_886_ = 1;
lean_inc(v_gen_885_);
lean_inc(v_ringId_884_);
v___x_887_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_887_, 0, v_ringId_884_);
lean_ctor_set(v___x_887_, 1, v_gen_885_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*2, v___x_886_);
lean_inc(v_a_882_);
lean_inc_ref(v_a_881_);
lean_inc(v_a_880_);
lean_inc_ref(v_a_879_);
lean_inc(v_a_878_);
lean_inc_ref(v_a_877_);
lean_inc(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc(v_a_873_);
v___x_888_ = lean_apply_12(v_x_871_, v___x_887_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, lean_box(0));
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_903_, lean_object* v_x_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_ringId_917_; lean_object* v_gen_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_ringId_917_ = lean_ctor_get(v_a_905_, 0);
v_gen_918_ = lean_ctor_get(v_a_905_, 1);
v___x_919_ = 1;
lean_inc(v_gen_918_);
lean_inc(v_ringId_917_);
v___x_920_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_920_, 0, v_ringId_917_);
lean_ctor_set(v___x_920_, 1, v_gen_918_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*2, v___x_919_);
lean_inc(v_a_915_);
lean_inc_ref(v_a_914_);
lean_inc(v_a_913_);
lean_inc_ref(v_a_912_);
lean_inc(v_a_911_);
lean_inc_ref(v_a_910_);
lean_inc(v_a_909_);
lean_inc_ref(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v_a_906_);
v___x_921_ = lean_apply_12(v_x_904_, v___x_920_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, lean_box(0));
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_922_, lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_922_, v_x_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_937_){
_start:
{
uint8_t v_checkCoeffDvd_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_checkCoeffDvd_939_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*2);
v___x_940_ = lean_box(v_checkCoeffDvd_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_942_);
lean_dec_ref(v_a_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_945_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = lean_array_get_size(v_keys_971_);
v___x_976_ = lean_nat_dec_lt(v_i_973_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_i_973_);
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
lean_object* v_k_x27_978_; size_t v___x_979_; size_t v___x_980_; uint8_t v___x_981_; 
v_k_x27_978_ = lean_array_fget_borrowed(v_keys_971_, v_i_973_);
v___x_979_ = lean_ptr_addr(v_k_974_);
v___x_980_ = lean_ptr_addr(v_k_x27_978_);
v___x_981_ = lean_usize_dec_eq(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_i_973_, v___x_982_);
lean_dec(v_i_973_);
v_i_973_ = v___x_983_;
goto _start;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_array_fget_borrowed(v_vals_972_, v_i_973_);
lean_dec(v_i_973_);
lean_inc(v___x_985_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_i_989_, lean_object* v_k_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_987_, v_vals_988_, v_i_989_, v_k_990_);
lean_dec_ref(v_k_990_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_992_, size_t v_x_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_992_) == 0)
{
lean_object* v_es_995_; lean_object* v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v_j_999_; lean_object* v___x_1000_; 
v_es_995_ = lean_ctor_get(v_x_992_, 0);
v___x_996_ = lean_box(2);
v___x_997_ = ((size_t)31ULL);
v___x_998_ = lean_usize_land(v_x_993_, v___x_997_);
v_j_999_ = lean_usize_to_nat(v___x_998_);
v___x_1000_ = lean_array_get_borrowed(v___x_996_, v_es_995_, v_j_999_);
lean_dec(v_j_999_);
switch(lean_obj_tag(v___x_1000_))
{
case 0:
{
lean_object* v_key_1001_; lean_object* v_val_1002_; size_t v___x_1003_; size_t v___x_1004_; uint8_t v___x_1005_; 
v_key_1001_ = lean_ctor_get(v___x_1000_, 0);
v_val_1002_ = lean_ctor_get(v___x_1000_, 1);
v___x_1003_ = lean_ptr_addr(v_x_994_);
v___x_1004_ = lean_ptr_addr(v_key_1001_);
v___x_1005_ = lean_usize_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; 
lean_inc(v_val_1002_);
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_val_1002_);
return v___x_1007_;
}
}
case 1:
{
lean_object* v_node_1008_; size_t v___x_1009_; size_t v___x_1010_; 
v_node_1008_ = lean_ctor_get(v___x_1000_, 0);
v___x_1009_ = ((size_t)5ULL);
v___x_1010_ = lean_usize_shift_right(v_x_993_, v___x_1009_);
v_x_992_ = v_node_1008_;
v_x_993_ = v___x_1010_;
goto _start;
}
default: 
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_box(0);
return v___x_1012_;
}
}
}
else
{
lean_object* v_ks_1013_; lean_object* v_vs_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_ks_1013_ = lean_ctor_get(v_x_992_, 0);
v_vs_1014_ = lean_ctor_get(v_x_992_, 1);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1013_, v_vs_1014_, v___x_1015_, v_x_994_);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
size_t v_x_905__boxed_1020_; lean_object* v_res_1021_; 
v_x_905__boxed_1020_ = lean_unbox_usize(v_x_1018_);
lean_dec(v_x_1018_);
v_res_1021_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1017_, v_x_905__boxed_1020_, v_x_1019_);
lean_dec_ref(v_x_1019_);
lean_dec_ref(v_x_1017_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; uint64_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1024_ = lean_ptr_addr(v_x_1023_);
v___x_1025_ = ((size_t)3ULL);
v___x_1026_ = lean_usize_shift_right(v___x_1024_, v___x_1025_);
v___x_1027_ = lean_usize_to_uint64(v___x_1026_);
v___x_1028_ = lean_uint64_to_usize(v___x_1027_);
v___x_1029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1022_, v___x_1028_, v_x_1023_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1030_, v_x_1031_);
lean_dec_ref(v_x_1031_);
lean_dec_ref(v_x_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1034_, v_a_1035_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_exprToRingId_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_exprToRingId_1042_ = lean_ctor_get(v_a_1038_, 1);
lean_inc_ref(v_exprToRingId_1042_);
lean_dec(v_a_1038_);
v___x_1043_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_1042_, v_e_1033_);
lean_dec_ref(v_exprToRingId_1042_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1045_ = v___x_1040_;
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
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1037_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1037_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1056_, v_a_1057_, v_a_1058_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_e_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1061_, v_a_1062_, v_a_1070_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_e_1074_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1088_, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_1091_, v_x_1092_, v_x_1093_);
lean_dec_ref(v_x_1093_);
lean_dec_ref(v_x_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, size_t v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1096_, v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
size_t v_x_1026__boxed_1104_; lean_object* v_res_1105_; 
v_x_1026__boxed_1104_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_res_1105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_1100_, v_x_1101_, v_x_1026__boxed_1104_, v_x_1103_);
lean_dec_ref(v_x_1103_);
lean_dec_ref(v_x_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1106_, lean_object* v_keys_1107_, lean_object* v_vals_1108_, lean_object* v_heq_1109_, lean_object* v_i_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1107_, v_vals_1108_, v_i_1110_, v_k_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_heq_1116_, lean_object* v_i_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1113_, v_keys_1114_, v_vals_1115_, v_heq_1116_, v_i_1117_, v_k_1118_);
lean_dec_ref(v_k_1118_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_1120_, lean_object* v_____do__lift_1121_){
_start:
{
lean_object* v_charInst_x3f_1125_; 
v_charInst_x3f_1125_ = lean_ctor_get(v_____do__lift_1121_, 5);
lean_inc(v_charInst_x3f_1125_);
lean_dec_ref(v_____do__lift_1121_);
if (lean_obj_tag(v_charInst_x3f_1125_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1137_; 
v_val_1126_ = lean_ctor_get(v_charInst_x3f_1125_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_charInst_x3f_1125_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1128_ = v_charInst_x3f_1125_;
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v_charInst_x3f_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1137_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_snd_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_snd_1130_ = lean_ctor_get(v_val_1126_, 1);
lean_inc(v_snd_1130_);
lean_dec(v_val_1126_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_nat_dec_eq(v_snd_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1134_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_snd_1130_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_snd_1130_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_apply_2(v_toPure_1120_, lean_box(0), v___x_1134_);
return v___x_1135_;
}
}
else
{
lean_dec(v_snd_1130_);
lean_del_object(v___x_1128_);
goto v___jp_1122_;
}
}
}
else
{
lean_dec(v_charInst_x3f_1125_);
goto v___jp_1122_;
}
v___jp_1122_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_apply_2(v_toPure_1120_, lean_box(0), v___x_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v_toApplicative_1140_; lean_object* v_toBind_1141_; lean_object* v_getRing_1142_; lean_object* v_toPure_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; 
v_toApplicative_1140_ = lean_ctor_get(v_inst_1138_, 0);
lean_inc_ref(v_toApplicative_1140_);
v_toBind_1141_ = lean_ctor_get(v_inst_1138_, 1);
lean_inc(v_toBind_1141_);
lean_dec_ref(v_inst_1138_);
v_getRing_1142_ = lean_ctor_get(v_inst_1139_, 0);
lean_inc(v_getRing_1142_);
lean_dec_ref(v_inst_1139_);
v_toPure_1143_ = lean_ctor_get(v_toApplicative_1140_, 1);
lean_inc(v_toPure_1143_);
lean_dec_ref(v_toApplicative_1140_);
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1144_, 0, v_toPure_1143_);
v___x_1145_ = lean_apply_4(v_toBind_1141_, lean_box(0), lean_box(0), v_getRing_1142_, v___f_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_1147_, v_inst_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_1150_, lean_object* v_____do__lift_1151_){
_start:
{
lean_object* v_charInst_x3f_1155_; 
v_charInst_x3f_1155_ = lean_ctor_get(v_____do__lift_1151_, 5);
lean_inc(v_charInst_x3f_1155_);
lean_dec_ref(v_____do__lift_1151_);
if (lean_obj_tag(v_charInst_x3f_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v_snd_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_val_1156_ = lean_ctor_get(v_charInst_x3f_1155_, 0);
v_snd_1157_ = lean_ctor_get(v_val_1156_, 1);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_nat_dec_eq(v_snd_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_apply_2(v_toPure_1150_, lean_box(0), v_charInst_x3f_1155_);
return v___x_1160_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_1155_, 1);
goto v___jp_1152_;
}
}
else
{
lean_dec(v_charInst_x3f_1155_);
goto v___jp_1152_;
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v_toApplicative_1163_; lean_object* v_toBind_1164_; lean_object* v_getRing_1165_; lean_object* v_toPure_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
v_toApplicative_1163_ = lean_ctor_get(v_inst_1161_, 0);
lean_inc_ref(v_toApplicative_1163_);
v_toBind_1164_ = lean_ctor_get(v_inst_1161_, 1);
lean_inc(v_toBind_1164_);
lean_dec_ref(v_inst_1161_);
v_getRing_1165_ = lean_ctor_get(v_inst_1162_, 0);
lean_inc(v_getRing_1165_);
lean_dec_ref(v_inst_1162_);
v_toPure_1166_ = lean_ctor_get(v_toApplicative_1163_, 1);
lean_inc(v_toPure_1166_);
lean_dec_ref(v_toApplicative_1163_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1167_, 0, v_toPure_1166_);
v___x_1168_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v_getRing_1165_, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_1170_, v_inst_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_noZeroDivInst_x3f_1190_; lean_object* v___x_1192_; 
v_noZeroDivInst_x3f_1190_ = lean_ctor_get(v_a_1186_, 6);
lean_inc(v_noZeroDivInst_x3f_1190_);
lean_dec(v_a_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_noZeroDivInst_x3f_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_noZeroDivInst_x3f_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
v_a_1195_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1185_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1185_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1244_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1244_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1244_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_noZeroDivInst_x3f_1233_; 
v_noZeroDivInst_x3f_1233_ = lean_ctor_get(v_a_1229_, 6);
lean_inc(v_noZeroDivInst_x3f_1233_);
lean_dec(v_a_1229_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1233_) == 0)
{
uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = 0;
v___x_1235_ = lean_box(v___x_1234_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
uint8_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1233_, 1);
v___x_1239_ = 1;
v___x_1240_ = lean_box(v___x_1239_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1240_);
v___x_1242_ = v___x_1231_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1228_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1228_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1295_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_toRing_1283_; lean_object* v_charInst_x3f_1284_; 
v_toRing_1283_ = lean_ctor_get(v_a_1279_, 0);
lean_inc_ref(v_toRing_1283_);
lean_dec(v_a_1279_);
v_charInst_x3f_1284_ = lean_ctor_get(v_toRing_1283_, 5);
lean_inc(v_charInst_x3f_1284_);
lean_dec_ref(v_toRing_1283_);
if (lean_obj_tag(v_charInst_x3f_1284_) == 0)
{
uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = 0;
v___x_1286_ = lean_box(v___x_1285_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1286_);
v___x_1288_ = v___x_1281_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
else
{
uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec_ref_known(v_charInst_x3f_1284_, 1);
v___x_1290_ = 1;
v___x_1291_ = lean_box(v___x_1290_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1291_);
v___x_1293_ = v___x_1281_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1278_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1278_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1345_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1345_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1345_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_toRing_1337_; lean_object* v_charInst_x3f_1338_; 
v_toRing_1337_ = lean_ctor_get(v_a_1333_, 0);
lean_inc_ref(v_toRing_1337_);
lean_dec(v_a_1333_);
v_charInst_x3f_1338_ = lean_ctor_get(v_toRing_1337_, 5);
lean_inc(v_charInst_x3f_1338_);
lean_dec_ref(v_toRing_1337_);
if (lean_obj_tag(v_charInst_x3f_1338_) == 1)
{
lean_object* v_val_1339_; lean_object* v___x_1341_; 
v_val_1339_ = lean_ctor_get(v_charInst_x3f_1338_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_charInst_x3f_1338_, 1);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_val_1339_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_val_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_charInst_x3f_1338_);
lean_del_object(v___x_1335_);
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1344_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1343_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1332_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1332_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1395_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1395_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1395_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fieldInst_x3f_1384_; 
v_fieldInst_x3f_1384_ = lean_ctor_get(v_a_1380_, 7);
lean_inc(v_fieldInst_x3f_1384_);
lean_dec(v_a_1380_);
if (lean_obj_tag(v_fieldInst_x3f_1384_) == 0)
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = 0;
v___x_1386_ = lean_box(v___x_1385_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1386_);
v___x_1388_ = v___x_1382_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec_ref_known(v_fieldInst_x3f_1384_, 1);
v___x_1390_ = 1;
v___x_1391_ = lean_box(v___x_1390_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1391_);
v___x_1393_ = v___x_1382_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1379_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1379_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1437_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1437_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1437_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_queue_1426_; 
v_queue_1426_ = lean_ctor_get(v_a_1422_, 4);
lean_inc(v_queue_1426_);
lean_dec(v_a_1422_);
if (lean_obj_tag(v_queue_1426_) == 0)
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec_ref_known(v_queue_1426_, 5);
v___x_1427_ = 0;
v___x_1428_ = lean_box(v___x_1427_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1428_);
v___x_1430_ = v___x_1424_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
else
{
uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = 1;
v___x_1433_ = lean_box(v___x_1432_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1433_);
v___x_1435_ = v___x_1424_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1421_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1421_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1451_, v_a_1452_, v_a_1460_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1477_, lean_object* v_t_1478_){
_start:
{
if (lean_obj_tag(v_t_1478_) == 0)
{
lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v_l_1481_; lean_object* v_r_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_2136_; 
v_k_1479_ = lean_ctor_get(v_t_1478_, 1);
v_v_1480_ = lean_ctor_get(v_t_1478_, 2);
v_l_1481_ = lean_ctor_get(v_t_1478_, 3);
v_r_1482_ = lean_ctor_get(v_t_1478_, 4);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_t_1478_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_t_1478_, 0);
lean_dec(v_unused_2137_);
v___x_1484_ = v_t_1478_;
v_isShared_1485_ = v_isSharedCheck_2136_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_r_1482_);
lean_inc(v_l_1481_);
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
lean_dec(v_t_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_2136_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1477_, v_k_1479_);
switch(v___x_1486_)
{
case 0:
{
lean_object* v_impl_1487_; lean_object* v___x_1488_; 
v_impl_1487_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1477_, v_l_1481_);
v___x_1488_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1487_) == 0)
{
if (lean_obj_tag(v_r_1482_) == 0)
{
lean_object* v_size_1489_; lean_object* v_size_1490_; lean_object* v_k_1491_; lean_object* v_v_1492_; lean_object* v_l_1493_; lean_object* v_r_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_size_1489_ = lean_ctor_get(v_impl_1487_, 0);
lean_inc(v_size_1489_);
v_size_1490_ = lean_ctor_get(v_r_1482_, 0);
v_k_1491_ = lean_ctor_get(v_r_1482_, 1);
v_v_1492_ = lean_ctor_get(v_r_1482_, 2);
v_l_1493_ = lean_ctor_get(v_r_1482_, 3);
lean_inc(v_l_1493_);
v_r_1494_ = lean_ctor_get(v_r_1482_, 4);
v___x_1495_ = lean_unsigned_to_nat(3u);
v___x_1496_ = lean_nat_mul(v___x_1495_, v_size_1489_);
v___x_1497_ = lean_nat_dec_lt(v___x_1496_, v_size_1490_);
lean_dec(v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_l_1493_);
v___x_1498_ = lean_nat_add(v___x_1488_, v_size_1489_);
lean_dec(v_size_1489_);
v___x_1499_ = lean_nat_add(v___x_1498_, v_size_1490_);
lean_dec(v___x_1498_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 3, v_impl_1487_);
lean_ctor_set(v___x_1484_, 0, v___x_1499_);
v___x_1501_ = v___x_1484_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_impl_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_r_1482_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
else
{
lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1566_; 
lean_inc(v_r_1494_);
lean_inc(v_v_1492_);
lean_inc(v_k_1491_);
lean_inc(v_size_1490_);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; lean_object* v_unused_1571_; 
v_unused_1567_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_r_1482_, 2);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_r_1482_, 1);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1571_);
v___x_1504_ = v_r_1482_;
v_isShared_1505_ = v_isSharedCheck_1566_;
goto v_resetjp_1503_;
}
else
{
lean_dec(v_r_1482_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1566_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_size_1506_; lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v_l_1509_; lean_object* v_r_1510_; lean_object* v_size_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_size_1506_ = lean_ctor_get(v_l_1493_, 0);
v_k_1507_ = lean_ctor_get(v_l_1493_, 1);
v_v_1508_ = lean_ctor_get(v_l_1493_, 2);
v_l_1509_ = lean_ctor_get(v_l_1493_, 3);
v_r_1510_ = lean_ctor_get(v_l_1493_, 4);
v_size_1511_ = lean_ctor_get(v_r_1494_, 0);
v___x_1512_ = lean_unsigned_to_nat(2u);
v___x_1513_ = lean_nat_mul(v___x_1512_, v_size_1511_);
v___x_1514_ = lean_nat_dec_lt(v_size_1506_, v___x_1513_);
lean_dec(v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1542_; 
lean_inc(v_r_1510_);
lean_inc(v_l_1509_);
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_l_1493_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1543_ = lean_ctor_get(v_l_1493_, 4);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1493_, 3);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1493_, 2);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_l_1493_, 1);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_l_1493_, 0);
lean_dec(v_unused_1547_);
v___x_1516_ = v_l_1493_;
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v_l_1493_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1532_; 
v___x_1518_ = lean_nat_add(v___x_1488_, v_size_1489_);
lean_dec(v_size_1489_);
v___x_1519_ = lean_nat_add(v___x_1518_, v_size_1490_);
lean_dec(v_size_1490_);
if (lean_obj_tag(v_l_1509_) == 0)
{
lean_object* v_size_1540_; 
v_size_1540_ = lean_ctor_get(v_l_1509_, 0);
lean_inc(v_size_1540_);
v___y_1532_ = v_size_1540_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___y_1532_ = v___x_1541_;
goto v___jp_1531_;
}
v___jp_1520_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_nat_add(v___y_1521_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec(v___y_1521_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 4, v_r_1494_);
lean_ctor_set(v___x_1516_, 3, v_r_1510_);
lean_ctor_set(v___x_1516_, 2, v_v_1492_);
lean_ctor_set(v___x_1516_, 1, v_k_1491_);
lean_ctor_set(v___x_1516_, 0, v___x_1524_);
v___x_1526_ = v___x_1516_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1491_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1492_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1510_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1494_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 4, v___x_1526_);
lean_ctor_set(v___x_1504_, 3, v___y_1522_);
lean_ctor_set(v___x_1504_, 2, v_v_1508_);
lean_ctor_set(v___x_1504_, 1, v_k_1507_);
lean_ctor_set(v___x_1504_, 0, v___x_1519_);
v___x_1528_ = v___x_1504_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v___y_1522_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
v___jp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_nat_add(v___x_1518_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec(v___x_1518_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_l_1509_);
lean_ctor_set(v___x_1484_, 3, v_impl_1487_);
lean_ctor_set(v___x_1484_, 0, v___x_1533_);
v___x_1535_ = v___x_1484_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_impl_1487_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_l_1509_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_nat_add(v___x_1488_, v_size_1511_);
if (lean_obj_tag(v_r_1510_) == 0)
{
lean_object* v_size_1537_; 
v_size_1537_ = lean_ctor_get(v_r_1510_, 0);
lean_inc(v_size_1537_);
v___y_1521_ = v___x_1536_;
v___y_1522_ = v___x_1535_;
v___y_1523_ = v_size_1537_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___y_1521_ = v___x_1536_;
v___y_1522_ = v___x_1535_;
v___y_1523_ = v___x_1538_;
goto v___jp_1520_;
}
}
}
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_del_object(v___x_1484_);
v___x_1548_ = lean_nat_add(v___x_1488_, v_size_1489_);
lean_dec(v_size_1489_);
v___x_1549_ = lean_nat_add(v___x_1548_, v_size_1490_);
lean_dec(v_size_1490_);
v___x_1550_ = lean_nat_add(v___x_1548_, v_size_1506_);
lean_dec(v___x_1548_);
lean_inc_ref(v_impl_1487_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 4, v_l_1493_);
lean_ctor_set(v___x_1504_, 3, v_impl_1487_);
lean_ctor_set(v___x_1504_, 2, v_v_1480_);
lean_ctor_set(v___x_1504_, 1, v_k_1479_);
lean_ctor_set(v___x_1504_, 0, v___x_1550_);
v___x_1552_ = v___x_1504_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_impl_1487_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_l_1493_);
v___x_1552_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v_impl_1487_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; 
v_unused_1560_ = lean_ctor_get(v_impl_1487_, 4);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_impl_1487_, 3);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_impl_1487_, 2);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_impl_1487_, 1);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_impl_1487_, 0);
lean_dec(v_unused_1564_);
v___x_1554_ = v_impl_1487_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_impl_1487_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v_r_1494_);
lean_ctor_set(v___x_1554_, 3, v___x_1552_);
lean_ctor_set(v___x_1554_, 2, v_v_1492_);
lean_ctor_set(v___x_1554_, 1, v_k_1491_);
lean_ctor_set(v___x_1554_, 0, v___x_1549_);
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1491_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1492_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_r_1494_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v_size_1572_ = lean_ctor_get(v_impl_1487_, 0);
lean_inc(v_size_1572_);
v___x_1573_ = lean_nat_add(v___x_1488_, v_size_1572_);
lean_dec(v_size_1572_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 3, v_impl_1487_);
lean_ctor_set(v___x_1484_, 0, v___x_1573_);
v___x_1575_ = v___x_1484_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_impl_1487_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_r_1482_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
if (lean_obj_tag(v_r_1482_) == 0)
{
lean_object* v_l_1577_; 
v_l_1577_ = lean_ctor_get(v_r_1482_, 3);
lean_inc(v_l_1577_);
if (lean_obj_tag(v_l_1577_) == 0)
{
lean_object* v_r_1578_; 
v_r_1578_ = lean_ctor_get(v_r_1482_, 4);
lean_inc(v_r_1578_);
if (lean_obj_tag(v_r_1578_) == 0)
{
lean_object* v_size_1579_; lean_object* v_k_1580_; lean_object* v_v_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1594_; 
v_size_1579_ = lean_ctor_get(v_r_1482_, 0);
v_k_1580_ = lean_ctor_get(v_r_1482_, 1);
v_v_1581_ = lean_ctor_get(v_r_1482_, 2);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1595_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1596_);
v___x_1583_ = v_r_1482_;
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_v_1581_);
lean_inc(v_k_1580_);
lean_inc(v_size_1579_);
lean_dec(v_r_1482_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_size_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v_size_1585_ = lean_ctor_get(v_l_1577_, 0);
v___x_1586_ = lean_nat_add(v___x_1488_, v_size_1579_);
lean_dec(v_size_1579_);
v___x_1587_ = lean_nat_add(v___x_1488_, v_size_1585_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_l_1577_);
lean_ctor_set(v___x_1583_, 3, v_impl_1487_);
lean_ctor_set(v___x_1583_, 2, v_v_1480_);
lean_ctor_set(v___x_1583_, 1, v_k_1479_);
lean_ctor_set(v___x_1583_, 0, v___x_1587_);
v___x_1589_ = v___x_1583_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_impl_1487_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_l_1577_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_r_1578_);
lean_ctor_set(v___x_1484_, 3, v___x_1589_);
lean_ctor_set(v___x_1484_, 2, v_v_1581_);
lean_ctor_set(v___x_1484_, 1, v_k_1580_);
lean_ctor_set(v___x_1484_, 0, v___x_1586_);
v___x_1591_ = v___x_1484_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1580_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1581_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_r_1578_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_k_1597_; lean_object* v_v_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1621_; 
v_k_1597_ = lean_ctor_get(v_r_1482_, 1);
v_v_1598_ = lean_ctor_get(v_r_1482_, 2);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; 
v_unused_1622_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1624_);
v___x_1600_ = v_r_1482_;
v_isShared_1601_ = v_isSharedCheck_1621_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_v_1598_);
lean_inc(v_k_1597_);
lean_dec(v_r_1482_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1621_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1617_; 
v_k_1602_ = lean_ctor_get(v_l_1577_, 1);
v_v_1603_ = lean_ctor_get(v_l_1577_, 2);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_l_1577_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; 
v_unused_1618_ = lean_ctor_get(v_l_1577_, 4);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_l_1577_, 3);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_l_1577_, 0);
lean_dec(v_unused_1620_);
v___x_1605_ = v_l_1577_;
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_v_1603_);
lean_inc(v_k_1602_);
lean_dec(v_l_1577_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_unsigned_to_nat(3u);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 4, v_r_1578_);
lean_ctor_set(v___x_1605_, 3, v_r_1578_);
lean_ctor_set(v___x_1605_, 2, v_v_1480_);
lean_ctor_set(v___x_1605_, 1, v_k_1479_);
lean_ctor_set(v___x_1605_, 0, v___x_1488_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_r_1578_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_r_1578_);
v___x_1609_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 3, v_r_1578_);
lean_ctor_set(v___x_1600_, 0, v___x_1488_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_r_1578_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_r_1578_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_1611_);
lean_ctor_set(v___x_1484_, 3, v___x_1609_);
lean_ctor_set(v___x_1484_, 2, v_v_1603_);
lean_ctor_set(v___x_1484_, 1, v_k_1602_);
lean_ctor_set(v___x_1484_, 0, v___x_1607_);
v___x_1613_ = v___x_1484_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1625_; 
v_r_1625_ = lean_ctor_get(v_r_1482_, 4);
lean_inc(v_r_1625_);
if (lean_obj_tag(v_r_1625_) == 0)
{
lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1638_; 
v_k_1626_ = lean_ctor_get(v_r_1482_, 1);
v_v_1627_ = lean_ctor_get(v_r_1482_, 2);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; 
v_unused_1639_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1641_);
v___x_1629_ = v_r_1482_;
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_v_1627_);
lean_inc(v_k_1626_);
lean_dec(v_r_1482_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_unsigned_to_nat(3u);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 4, v_l_1577_);
lean_ctor_set(v___x_1629_, 2, v_v_1480_);
lean_ctor_set(v___x_1629_, 1, v_k_1479_);
lean_ctor_set(v___x_1629_, 0, v___x_1488_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_l_1577_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_l_1577_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_r_1625_);
lean_ctor_set(v___x_1484_, 3, v___x_1633_);
lean_ctor_set(v___x_1484_, 2, v_v_1627_);
lean_ctor_set(v___x_1484_, 1, v_k_1626_);
lean_ctor_set(v___x_1484_, 0, v___x_1631_);
v___x_1635_ = v___x_1484_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_r_1625_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_size_1642_; lean_object* v_k_1643_; lean_object* v_v_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1655_; 
v_size_1642_ = lean_ctor_get(v_r_1482_, 0);
v_k_1643_ = lean_ctor_get(v_r_1482_, 1);
v_v_1644_ = lean_ctor_get(v_r_1482_, 2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1656_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1657_);
v___x_1646_ = v_r_1482_;
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_v_1644_);
lean_inc(v_k_1643_);
lean_inc(v_size_1642_);
lean_dec(v_r_1482_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1655_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 3, v_r_1625_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_size_1642_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1643_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1644_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_r_1625_);
v___x_1649_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(2u);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_1649_);
lean_ctor_set(v___x_1484_, 3, v_r_1625_);
lean_ctor_set(v___x_1484_, 0, v___x_1650_);
v___x_1652_ = v___x_1484_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v_r_1625_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v___x_1649_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
else
{
lean_object* v___x_1659_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 3, v_r_1482_);
lean_ctor_set(v___x_1484_, 0, v___x_1488_);
v___x_1659_ = v___x_1484_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_r_1482_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1482_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1484_);
lean_dec(v_v_1480_);
lean_dec(v_k_1479_);
if (lean_obj_tag(v_l_1481_) == 0)
{
if (lean_obj_tag(v_r_1482_) == 0)
{
lean_object* v_size_1661_; lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v_l_1664_; lean_object* v_r_1665_; lean_object* v_size_1666_; lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v_l_1669_; lean_object* v_r_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_size_1661_ = lean_ctor_get(v_l_1481_, 0);
v_k_1662_ = lean_ctor_get(v_l_1481_, 1);
v_v_1663_ = lean_ctor_get(v_l_1481_, 2);
v_l_1664_ = lean_ctor_get(v_l_1481_, 3);
v_r_1665_ = lean_ctor_get(v_l_1481_, 4);
lean_inc(v_r_1665_);
v_size_1666_ = lean_ctor_get(v_r_1482_, 0);
v_k_1667_ = lean_ctor_get(v_r_1482_, 1);
v_v_1668_ = lean_ctor_get(v_r_1482_, 2);
v_l_1669_ = lean_ctor_get(v_r_1482_, 3);
lean_inc(v_l_1669_);
v_r_1670_ = lean_ctor_get(v_r_1482_, 4);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_dec_lt(v_size_1661_, v_size_1666_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1808_; 
lean_inc(v_l_1664_);
lean_inc(v_v_1663_);
lean_inc(v_k_1662_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; lean_object* v_unused_1810_; lean_object* v_unused_1811_; lean_object* v_unused_1812_; lean_object* v_unused_1813_; 
v_unused_1809_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_l_1481_, 2);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_l_1481_, 1);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_1813_);
v___x_1674_ = v_l_1481_;
v_isShared_1675_ = v_isSharedCheck_1808_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_l_1481_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1808_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v_tree_1677_; 
v___x_1676_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1662_, v_v_1663_, v_l_1664_, v_r_1665_);
v_tree_1677_ = lean_ctor_get(v___x_1676_, 2);
lean_inc(v_tree_1677_);
if (lean_obj_tag(v_tree_1677_) == 0)
{
lean_object* v_k_1678_; lean_object* v_v_1679_; lean_object* v_size_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_k_1678_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_k_1678_);
v_v_1679_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_v_1679_);
lean_dec_ref(v___x_1676_);
v_size_1680_ = lean_ctor_get(v_tree_1677_, 0);
v___x_1681_ = lean_unsigned_to_nat(3u);
v___x_1682_ = lean_nat_mul(v___x_1681_, v_size_1680_);
v___x_1683_ = lean_nat_dec_lt(v___x_1682_, v_size_1666_);
lean_dec(v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec(v_l_1669_);
v___x_1684_ = lean_nat_add(v___x_1671_, v_size_1680_);
v___x_1685_ = lean_nat_add(v___x_1684_, v_size_1666_);
lean_dec(v___x_1684_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_r_1482_);
lean_ctor_set(v___x_1674_, 3, v_tree_1677_);
lean_ctor_set(v___x_1674_, 2, v_v_1679_);
lean_ctor_set(v___x_1674_, 1, v_k_1678_);
lean_ctor_set(v___x_1674_, 0, v___x_1685_);
v___x_1687_ = v___x_1674_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1678_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1679_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_tree_1677_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_r_1482_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
else
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1743_; 
lean_inc(v_r_1670_);
lean_inc(v_v_1668_);
lean_inc(v_k_1667_);
lean_inc(v_size_1666_);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1744_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_r_1482_, 2);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_r_1482_, 1);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1748_);
v___x_1690_ = v_r_1482_;
v_isShared_1691_ = v_isSharedCheck_1743_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v_r_1482_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1743_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_size_1692_; lean_object* v_k_1693_; lean_object* v_v_1694_; lean_object* v_l_1695_; lean_object* v_r_1696_; lean_object* v_size_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_size_1692_ = lean_ctor_get(v_l_1669_, 0);
v_k_1693_ = lean_ctor_get(v_l_1669_, 1);
v_v_1694_ = lean_ctor_get(v_l_1669_, 2);
v_l_1695_ = lean_ctor_get(v_l_1669_, 3);
v_r_1696_ = lean_ctor_get(v_l_1669_, 4);
v_size_1697_ = lean_ctor_get(v_r_1670_, 0);
v___x_1698_ = lean_unsigned_to_nat(2u);
v___x_1699_ = lean_nat_mul(v___x_1698_, v_size_1697_);
v___x_1700_ = lean_nat_dec_lt(v_size_1692_, v___x_1699_);
lean_dec(v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1728_; 
lean_inc(v_r_1696_);
lean_inc(v_l_1695_);
lean_inc(v_v_1694_);
lean_inc(v_k_1693_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_l_1669_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; lean_object* v_unused_1730_; lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; 
v_unused_1729_ = lean_ctor_get(v_l_1669_, 4);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_l_1669_, 3);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_l_1669_, 2);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_l_1669_, 1);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_l_1669_, 0);
lean_dec(v_unused_1733_);
v___x_1702_ = v_l_1669_;
v_isShared_1703_ = v_isSharedCheck_1728_;
goto v_resetjp_1701_;
}
else
{
lean_dec(v_l_1669_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1728_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1718_; 
v___x_1704_ = lean_nat_add(v___x_1671_, v_size_1680_);
v___x_1705_ = lean_nat_add(v___x_1704_, v_size_1666_);
lean_dec(v_size_1666_);
if (lean_obj_tag(v_l_1695_) == 0)
{
lean_object* v_size_1726_; 
v_size_1726_ = lean_ctor_get(v_l_1695_, 0);
lean_inc(v_size_1726_);
v___y_1718_ = v_size_1726_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___y_1718_ = v___x_1727_;
goto v___jp_1717_;
}
v___jp_1706_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_nat_add(v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec(v___y_1708_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 4, v_r_1670_);
lean_ctor_set(v___x_1702_, 3, v_r_1696_);
lean_ctor_set(v___x_1702_, 2, v_v_1668_);
lean_ctor_set(v___x_1702_, 1, v_k_1667_);
lean_ctor_set(v___x_1702_, 0, v___x_1710_);
v___x_1712_ = v___x_1702_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_r_1696_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_r_1670_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v___x_1712_);
lean_ctor_set(v___x_1690_, 3, v___y_1707_);
lean_ctor_set(v___x_1690_, 2, v_v_1694_);
lean_ctor_set(v___x_1690_, 1, v_k_1693_);
lean_ctor_set(v___x_1690_, 0, v___x_1705_);
v___x_1714_ = v___x_1690_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_k_1693_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_v_1694_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v___y_1707_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_nat_add(v___x_1704_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec(v___x_1704_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_l_1695_);
lean_ctor_set(v___x_1674_, 3, v_tree_1677_);
lean_ctor_set(v___x_1674_, 2, v_v_1679_);
lean_ctor_set(v___x_1674_, 1, v_k_1678_);
lean_ctor_set(v___x_1674_, 0, v___x_1719_);
v___x_1721_ = v___x_1674_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1678_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1679_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_tree_1677_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_l_1695_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_nat_add(v___x_1671_, v_size_1697_);
if (lean_obj_tag(v_r_1696_) == 0)
{
lean_object* v_size_1723_; 
v_size_1723_ = lean_ctor_get(v_r_1696_, 0);
lean_inc(v_size_1723_);
v___y_1707_ = v___x_1721_;
v___y_1708_ = v___x_1722_;
v___y_1709_ = v_size_1723_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___y_1707_ = v___x_1721_;
v___y_1708_ = v___x_1722_;
v___y_1709_ = v___x_1724_;
goto v___jp_1706_;
}
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1734_ = lean_nat_add(v___x_1671_, v_size_1680_);
v___x_1735_ = lean_nat_add(v___x_1734_, v_size_1666_);
lean_dec(v_size_1666_);
v___x_1736_ = lean_nat_add(v___x_1734_, v_size_1692_);
lean_dec(v___x_1734_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v_l_1669_);
lean_ctor_set(v___x_1690_, 3, v_tree_1677_);
lean_ctor_set(v___x_1690_, 2, v_v_1679_);
lean_ctor_set(v___x_1690_, 1, v_k_1678_);
lean_ctor_set(v___x_1690_, 0, v___x_1736_);
v___x_1738_ = v___x_1690_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_k_1678_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_v_1679_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_tree_1677_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_l_1669_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_r_1670_);
lean_ctor_set(v___x_1674_, 3, v___x_1738_);
lean_ctor_set(v___x_1674_, 2, v_v_1668_);
lean_ctor_set(v___x_1674_, 1, v_k_1667_);
lean_ctor_set(v___x_1674_, 0, v___x_1735_);
v___x_1740_ = v___x_1674_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_r_1670_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
else
{
lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1802_; 
lean_inc(v_r_1670_);
lean_inc(v_v_1668_);
lean_inc(v_k_1667_);
lean_inc(v_size_1666_);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; 
v_unused_1803_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_r_1482_, 2);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_r_1482_, 1);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1807_);
v___x_1750_ = v_r_1482_;
v_isShared_1751_ = v_isSharedCheck_1802_;
goto v_resetjp_1749_;
}
else
{
lean_dec(v_r_1482_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1802_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
if (lean_obj_tag(v_l_1669_) == 0)
{
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_k_1752_; lean_object* v_v_1753_; lean_object* v_size_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v_k_1752_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_k_1752_);
v_v_1753_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_v_1753_);
lean_dec_ref(v___x_1676_);
v_size_1754_ = lean_ctor_get(v_l_1669_, 0);
v___x_1755_ = lean_nat_add(v___x_1671_, v_size_1666_);
lean_dec(v_size_1666_);
v___x_1756_ = lean_nat_add(v___x_1671_, v_size_1754_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 4, v_l_1669_);
lean_ctor_set(v___x_1750_, 3, v_tree_1677_);
lean_ctor_set(v___x_1750_, 2, v_v_1753_);
lean_ctor_set(v___x_1750_, 1, v_k_1752_);
lean_ctor_set(v___x_1750_, 0, v___x_1756_);
v___x_1758_ = v___x_1750_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1752_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1753_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_tree_1677_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_l_1669_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_r_1670_);
lean_ctor_set(v___x_1674_, 3, v___x_1758_);
lean_ctor_set(v___x_1674_, 2, v_v_1668_);
lean_ctor_set(v___x_1674_, 1, v_k_1667_);
lean_ctor_set(v___x_1674_, 0, v___x_1755_);
v___x_1760_ = v___x_1674_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_r_1670_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_k_1763_; lean_object* v_v_1764_; lean_object* v_k_1765_; lean_object* v_v_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_size_1666_);
v_k_1763_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_k_1763_);
v_v_1764_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_v_1764_);
lean_dec_ref(v___x_1676_);
v_k_1765_ = lean_ctor_get(v_l_1669_, 1);
v_v_1766_ = lean_ctor_get(v_l_1669_, 2);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_l_1669_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; 
v_unused_1781_ = lean_ctor_get(v_l_1669_, 4);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_l_1669_, 3);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v_l_1669_, 0);
lean_dec(v_unused_1783_);
v___x_1768_ = v_l_1669_;
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_v_1766_);
lean_inc(v_k_1765_);
lean_dec(v_l_1669_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = lean_unsigned_to_nat(3u);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 4, v_r_1670_);
lean_ctor_set(v___x_1768_, 3, v_r_1670_);
lean_ctor_set(v___x_1768_, 2, v_v_1764_);
lean_ctor_set(v___x_1768_, 1, v_k_1763_);
lean_ctor_set(v___x_1768_, 0, v___x_1671_);
v___x_1772_ = v___x_1768_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1763_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1764_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_r_1670_);
v___x_1772_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 3, v_r_1670_);
lean_ctor_set(v___x_1750_, 0, v___x_1671_);
v___x_1774_ = v___x_1750_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_r_1670_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v___x_1774_);
lean_ctor_set(v___x_1674_, 3, v___x_1772_);
lean_ctor_set(v___x_1674_, 2, v_v_1766_);
lean_ctor_set(v___x_1674_, 1, v_k_1765_);
lean_ctor_set(v___x_1674_, 0, v___x_1770_);
v___x_1776_ = v___x_1674_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_k_1765_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_v_1766_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_k_1784_; lean_object* v_v_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec(v_size_1666_);
v_k_1784_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_k_1784_);
v_v_1785_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_v_1785_);
lean_dec_ref(v___x_1676_);
v___x_1786_ = lean_unsigned_to_nat(3u);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 4, v_l_1669_);
lean_ctor_set(v___x_1750_, 2, v_v_1785_);
lean_ctor_set(v___x_1750_, 1, v_k_1784_);
lean_ctor_set(v___x_1750_, 0, v___x_1671_);
v___x_1788_ = v___x_1750_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_l_1669_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_l_1669_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_r_1670_);
lean_ctor_set(v___x_1674_, 3, v___x_1788_);
lean_ctor_set(v___x_1674_, 2, v_v_1668_);
lean_ctor_set(v___x_1674_, 1, v_k_1667_);
lean_ctor_set(v___x_1674_, 0, v___x_1786_);
v___x_1790_ = v___x_1674_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_r_1670_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v_k_1793_; lean_object* v_v_1794_; lean_object* v___x_1796_; 
v_k_1793_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_k_1793_);
v_v_1794_ = lean_ctor_get(v___x_1676_, 1);
lean_inc(v_v_1794_);
lean_dec_ref(v___x_1676_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 3, v_r_1670_);
v___x_1796_ = v___x_1750_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_size_1666_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_r_1670_);
v___x_1796_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1797_ = lean_unsigned_to_nat(2u);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v___x_1796_);
lean_ctor_set(v___x_1674_, 3, v_r_1670_);
lean_ctor_set(v___x_1674_, 2, v_v_1794_);
lean_ctor_set(v___x_1674_, 1, v_k_1793_);
lean_ctor_set(v___x_1674_, 0, v___x_1797_);
v___x_1799_ = v___x_1674_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_k_1793_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_v_1794_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_r_1670_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v___x_1796_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
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
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1966_; 
lean_inc(v_r_1670_);
lean_inc(v_v_1668_);
lean_inc(v_k_1667_);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; 
v_unused_1967_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_r_1482_, 2);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_r_1482_, 1);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1971_);
v___x_1815_ = v_r_1482_;
v_isShared_1816_ = v_isSharedCheck_1966_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v_r_1482_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1966_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v_tree_1818_; 
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1667_, v_v_1668_, v_l_1669_, v_r_1670_);
v_tree_1818_ = lean_ctor_get(v___x_1817_, 2);
lean_inc(v_tree_1818_);
if (lean_obj_tag(v_tree_1818_) == 0)
{
lean_object* v_k_1819_; lean_object* v_v_1820_; lean_object* v_size_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_k_1819_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_k_1819_);
v_v_1820_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_v_1820_);
lean_dec_ref(v___x_1817_);
v_size_1821_ = lean_ctor_get(v_tree_1818_, 0);
v___x_1822_ = lean_unsigned_to_nat(3u);
v___x_1823_ = lean_nat_mul(v___x_1822_, v_size_1821_);
v___x_1824_ = lean_nat_dec_lt(v___x_1823_, v_size_1661_);
lean_dec(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_r_1665_);
v___x_1825_ = lean_nat_add(v___x_1671_, v_size_1661_);
v___x_1826_ = lean_nat_add(v___x_1825_, v_size_1821_);
lean_dec(v___x_1825_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_tree_1818_);
lean_ctor_set(v___x_1815_, 3, v_l_1481_);
lean_ctor_set(v___x_1815_, 2, v_v_1820_);
lean_ctor_set(v___x_1815_, 1, v_k_1819_);
lean_ctor_set(v___x_1815_, 0, v___x_1826_);
v___x_1828_ = v___x_1815_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_k_1819_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_v_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_tree_1818_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1895_; 
lean_inc(v_l_1664_);
lean_inc(v_v_1663_);
lean_inc(v_k_1662_);
lean_inc(v_size_1661_);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; 
v_unused_1896_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_l_1481_, 2);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1481_, 1);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_1900_);
v___x_1831_ = v_l_1481_;
v_isShared_1832_ = v_isSharedCheck_1895_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_l_1481_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1895_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_size_1833_; lean_object* v_size_1834_; lean_object* v_k_1835_; lean_object* v_v_1836_; lean_object* v_l_1837_; lean_object* v_r_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_size_1833_ = lean_ctor_get(v_l_1664_, 0);
v_size_1834_ = lean_ctor_get(v_r_1665_, 0);
v_k_1835_ = lean_ctor_get(v_r_1665_, 1);
v_v_1836_ = lean_ctor_get(v_r_1665_, 2);
v_l_1837_ = lean_ctor_get(v_r_1665_, 3);
v_r_1838_ = lean_ctor_get(v_r_1665_, 4);
v___x_1839_ = lean_unsigned_to_nat(2u);
v___x_1840_ = lean_nat_mul(v___x_1839_, v_size_1833_);
v___x_1841_ = lean_nat_dec_lt(v_size_1834_, v___x_1840_);
lean_dec(v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1879_; 
lean_inc(v_r_1838_);
lean_inc(v_l_1837_);
lean_inc(v_v_1836_);
lean_inc(v_k_1835_);
lean_del_object(v___x_1831_);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_r_1665_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; 
v_unused_1880_ = lean_ctor_get(v_r_1665_, 4);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_r_1665_, 3);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_r_1665_, 2);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_r_1665_, 1);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_r_1665_, 0);
lean_dec(v_unused_1884_);
v___x_1843_ = v_r_1665_;
v_isShared_1844_ = v_isSharedCheck_1879_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_r_1665_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1879_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___x_1867_; lean_object* v___y_1869_; 
v___x_1845_ = lean_nat_add(v___x_1671_, v_size_1661_);
lean_dec(v_size_1661_);
v___x_1846_ = lean_nat_add(v___x_1845_, v_size_1821_);
lean_dec(v___x_1845_);
v___x_1867_ = lean_nat_add(v___x_1671_, v_size_1833_);
if (lean_obj_tag(v_l_1837_) == 0)
{
lean_object* v_size_1877_; 
v_size_1877_ = lean_ctor_get(v_l_1837_, 0);
lean_inc(v_size_1877_);
v___y_1869_ = v_size_1877_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___y_1869_ = v___x_1878_;
goto v___jp_1868_;
}
v___jp_1847_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_nat_add(v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
lean_inc_ref(v_tree_1818_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 4, v_tree_1818_);
lean_ctor_set(v___x_1843_, 3, v_r_1838_);
lean_ctor_set(v___x_1843_, 2, v_v_1820_);
lean_ctor_set(v___x_1843_, 1, v_k_1819_);
lean_ctor_set(v___x_1843_, 0, v___x_1851_);
v___x_1853_ = v___x_1843_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1819_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1820_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_r_1838_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_tree_1818_);
v___x_1853_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_isSharedCheck_1860_ = !lean_is_exclusive(v_tree_1818_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1861_ = lean_ctor_get(v_tree_1818_, 4);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_tree_1818_, 3);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_tree_1818_, 2);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_tree_1818_, 1);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_tree_1818_, 0);
lean_dec(v_unused_1865_);
v___x_1855_ = v_tree_1818_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v_tree_1818_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 4, v___x_1853_);
lean_ctor_set(v___x_1855_, 3, v___y_1848_);
lean_ctor_set(v___x_1855_, 2, v_v_1836_);
lean_ctor_set(v___x_1855_, 1, v_k_1835_);
lean_ctor_set(v___x_1855_, 0, v___x_1846_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_k_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_v_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v___y_1848_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v___x_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
v___jp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_nat_add(v___x_1867_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec(v___x_1867_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_l_1837_);
lean_ctor_set(v___x_1815_, 3, v_l_1664_);
lean_ctor_set(v___x_1815_, 2, v_v_1663_);
lean_ctor_set(v___x_1815_, 1, v_k_1662_);
lean_ctor_set(v___x_1815_, 0, v___x_1870_);
v___x_1872_ = v___x_1815_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_l_1837_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_nat_add(v___x_1671_, v_size_1821_);
if (lean_obj_tag(v_r_1838_) == 0)
{
lean_object* v_size_1874_; 
v_size_1874_ = lean_ctor_get(v_r_1838_, 0);
lean_inc(v_size_1874_);
v___y_1848_ = v___x_1872_;
v___y_1849_ = v___x_1873_;
v___y_1850_ = v_size_1874_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___y_1848_ = v___x_1872_;
v___y_1849_ = v___x_1873_;
v___y_1850_ = v___x_1875_;
goto v___jp_1847_;
}
}
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1885_ = lean_nat_add(v___x_1671_, v_size_1661_);
lean_dec(v_size_1661_);
v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1821_);
lean_dec(v___x_1885_);
v___x_1887_ = lean_nat_add(v___x_1671_, v_size_1821_);
v___x_1888_ = lean_nat_add(v___x_1887_, v_size_1834_);
lean_dec(v___x_1887_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_tree_1818_);
lean_ctor_set(v___x_1815_, 3, v_r_1665_);
lean_ctor_set(v___x_1815_, 2, v_v_1820_);
lean_ctor_set(v___x_1815_, 1, v_k_1819_);
lean_ctor_set(v___x_1815_, 0, v___x_1888_);
v___x_1890_ = v___x_1815_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1819_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1820_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_r_1665_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_tree_1818_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v___x_1890_);
lean_ctor_set(v___x_1831_, 0, v___x_1886_);
v___x_1892_ = v___x_1831_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1664_) == 0)
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1924_; 
lean_inc_ref(v_l_1664_);
lean_inc(v_v_1663_);
lean_inc(v_k_1662_);
lean_inc(v_size_1661_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; lean_object* v_unused_1928_; lean_object* v_unused_1929_; 
v_unused_1925_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_l_1481_, 2);
lean_dec(v_unused_1927_);
v_unused_1928_ = lean_ctor_get(v_l_1481_, 1);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_1929_);
v___x_1902_ = v_l_1481_;
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v_l_1481_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
if (lean_obj_tag(v_r_1665_) == 0)
{
lean_object* v_k_1904_; lean_object* v_v_1905_; lean_object* v_size_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v_k_1904_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_k_1904_);
v_v_1905_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_v_1905_);
lean_dec_ref(v___x_1817_);
v_size_1906_ = lean_ctor_get(v_r_1665_, 0);
v___x_1907_ = lean_nat_add(v___x_1671_, v_size_1661_);
lean_dec(v_size_1661_);
v___x_1908_ = lean_nat_add(v___x_1671_, v_size_1906_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_tree_1818_);
lean_ctor_set(v___x_1815_, 3, v_r_1665_);
lean_ctor_set(v___x_1815_, 2, v_v_1905_);
lean_ctor_set(v___x_1815_, 1, v_k_1904_);
lean_ctor_set(v___x_1815_, 0, v___x_1908_);
v___x_1910_ = v___x_1815_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1905_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_r_1665_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_tree_1818_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 4, v___x_1910_);
lean_ctor_set(v___x_1902_, 0, v___x_1907_);
v___x_1912_ = v___x_1902_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec(v_size_1661_);
v_k_1915_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_k_1915_);
v_v_1916_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_v_1916_);
lean_dec_ref(v___x_1817_);
v___x_1917_ = lean_unsigned_to_nat(3u);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_r_1665_);
lean_ctor_set(v___x_1815_, 3, v_r_1665_);
lean_ctor_set(v___x_1815_, 2, v_v_1916_);
lean_ctor_set(v___x_1815_, 1, v_k_1915_);
lean_ctor_set(v___x_1815_, 0, v___x_1671_);
v___x_1919_ = v___x_1815_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1915_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1916_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_r_1665_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_r_1665_);
v___x_1919_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 4, v___x_1919_);
lean_ctor_set(v___x_1902_, 0, v___x_1917_);
v___x_1921_ = v___x_1902_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1665_) == 0)
{
lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1954_; 
lean_inc(v_l_1664_);
lean_inc(v_v_1663_);
lean_inc(v_k_1662_);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; lean_object* v_unused_1959_; 
v_unused_1955_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_l_1481_, 2);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_l_1481_, 1);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_1959_);
v___x_1931_ = v_l_1481_;
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v_l_1481_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_k_1933_; lean_object* v_v_1934_; lean_object* v_k_1935_; lean_object* v_v_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1950_; 
v_k_1933_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_k_1933_);
v_v_1934_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_v_1934_);
lean_dec_ref(v___x_1817_);
v_k_1935_ = lean_ctor_get(v_r_1665_, 1);
v_v_1936_ = lean_ctor_get(v_r_1665_, 2);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_r_1665_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1951_ = lean_ctor_get(v_r_1665_, 4);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_r_1665_, 3);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_r_1665_, 0);
lean_dec(v_unused_1953_);
v___x_1938_ = v_r_1665_;
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_v_1936_);
lean_inc(v_k_1935_);
lean_dec(v_r_1665_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1950_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_unsigned_to_nat(3u);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 4, v_l_1664_);
lean_ctor_set(v___x_1938_, 3, v_l_1664_);
lean_ctor_set(v___x_1938_, 2, v_v_1663_);
lean_ctor_set(v___x_1938_, 1, v_k_1662_);
lean_ctor_set(v___x_1938_, 0, v___x_1671_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_l_1664_);
v___x_1942_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_l_1664_);
lean_ctor_set(v___x_1815_, 3, v_l_1664_);
lean_ctor_set(v___x_1815_, 2, v_v_1934_);
lean_ctor_set(v___x_1815_, 1, v_k_1933_);
lean_ctor_set(v___x_1815_, 0, v___x_1671_);
v___x_1944_ = v___x_1815_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1934_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_l_1664_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_l_1664_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 4, v___x_1944_);
lean_ctor_set(v___x_1931_, 3, v___x_1942_);
lean_ctor_set(v___x_1931_, 2, v_v_1936_);
lean_ctor_set(v___x_1931_, 1, v_k_1935_);
lean_ctor_set(v___x_1931_, 0, v___x_1940_);
v___x_1946_ = v___x_1931_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1935_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1936_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
else
{
lean_object* v_k_1960_; lean_object* v_v_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v_k_1960_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_k_1960_);
v_v_1961_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_v_1961_);
lean_dec_ref(v___x_1817_);
v___x_1962_ = lean_unsigned_to_nat(2u);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 4, v_r_1665_);
lean_ctor_set(v___x_1815_, 3, v_l_1481_);
lean_ctor_set(v___x_1815_, 2, v_v_1961_);
lean_ctor_set(v___x_1815_, 1, v_k_1960_);
lean_ctor_set(v___x_1815_, 0, v___x_1962_);
v___x_1964_ = v___x_1815_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_k_1960_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_v_1961_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v_r_1665_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
}
else
{
return v_l_1481_;
}
}
else
{
return v_r_1482_;
}
}
default: 
{
lean_object* v_impl_1972_; lean_object* v___x_1973_; 
v_impl_1972_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1477_, v_r_1482_);
v___x_1973_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1972_) == 0)
{
if (lean_obj_tag(v_l_1481_) == 0)
{
lean_object* v_size_1974_; lean_object* v_size_1975_; lean_object* v_k_1976_; lean_object* v_v_1977_; lean_object* v_l_1978_; lean_object* v_r_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_size_1974_ = lean_ctor_get(v_impl_1972_, 0);
lean_inc(v_size_1974_);
v_size_1975_ = lean_ctor_get(v_l_1481_, 0);
v_k_1976_ = lean_ctor_get(v_l_1481_, 1);
v_v_1977_ = lean_ctor_get(v_l_1481_, 2);
v_l_1978_ = lean_ctor_get(v_l_1481_, 3);
v_r_1979_ = lean_ctor_get(v_l_1481_, 4);
lean_inc(v_r_1979_);
v___x_1980_ = lean_unsigned_to_nat(3u);
v___x_1981_ = lean_nat_mul(v___x_1980_, v_size_1974_);
v___x_1982_ = lean_nat_dec_lt(v___x_1981_, v_size_1975_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_dec(v_r_1979_);
v___x_1983_ = lean_nat_add(v___x_1973_, v_size_1975_);
v___x_1984_ = lean_nat_add(v___x_1983_, v_size_1974_);
lean_dec(v_size_1974_);
lean_dec(v___x_1983_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_impl_1972_);
lean_ctor_set(v___x_1484_, 0, v___x_1984_);
v___x_1986_ = v___x_1484_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_impl_1972_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2053_; 
lean_inc(v_l_1978_);
lean_inc(v_v_1977_);
lean_inc(v_k_1976_);
lean_inc(v_size_1975_);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; lean_object* v_unused_2058_; 
v_unused_2054_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_1481_, 2);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_l_1481_, 1);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_2058_);
v___x_1989_ = v_l_1481_;
v_isShared_1990_ = v_isSharedCheck_2053_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v_l_1481_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2053_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_size_1991_; lean_object* v_size_1992_; lean_object* v_k_1993_; lean_object* v_v_1994_; lean_object* v_l_1995_; lean_object* v_r_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_size_1991_ = lean_ctor_get(v_l_1978_, 0);
v_size_1992_ = lean_ctor_get(v_r_1979_, 0);
v_k_1993_ = lean_ctor_get(v_r_1979_, 1);
v_v_1994_ = lean_ctor_get(v_r_1979_, 2);
v_l_1995_ = lean_ctor_get(v_r_1979_, 3);
v_r_1996_ = lean_ctor_get(v_r_1979_, 4);
v___x_1997_ = lean_unsigned_to_nat(2u);
v___x_1998_ = lean_nat_mul(v___x_1997_, v_size_1991_);
v___x_1999_ = lean_nat_dec_lt(v_size_1992_, v___x_1998_);
lean_dec(v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2028_; 
lean_inc(v_r_1996_);
lean_inc(v_l_1995_);
lean_inc(v_v_1994_);
lean_inc(v_k_1993_);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_r_1979_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; 
v_unused_2029_ = lean_ctor_get(v_r_1979_, 4);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1979_, 3);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1979_, 2);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1979_, 1);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_1979_, 0);
lean_dec(v_unused_2033_);
v___x_2001_ = v_r_1979_;
v_isShared_2002_ = v_isSharedCheck_2028_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_r_1979_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2028_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___x_2016_; lean_object* v___y_2018_; 
v___x_2003_ = lean_nat_add(v___x_1973_, v_size_1975_);
lean_dec(v_size_1975_);
v___x_2004_ = lean_nat_add(v___x_2003_, v_size_1974_);
lean_dec(v___x_2003_);
v___x_2016_ = lean_nat_add(v___x_1973_, v_size_1991_);
if (lean_obj_tag(v_l_1995_) == 0)
{
lean_object* v_size_2026_; 
v_size_2026_ = lean_ctor_get(v_l_1995_, 0);
lean_inc(v_size_2026_);
v___y_2018_ = v_size_2026_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
v___y_2018_ = v___x_2027_;
goto v___jp_2017_;
}
v___jp_2005_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_nat_add(v___y_2006_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec(v___y_2006_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_impl_1972_);
lean_ctor_set(v___x_2001_, 3, v_r_1996_);
lean_ctor_set(v___x_2001_, 2, v_v_1480_);
lean_ctor_set(v___x_2001_, 1, v_k_1479_);
lean_ctor_set(v___x_2001_, 0, v___x_2009_);
v___x_2011_ = v___x_2001_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_r_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_impl_1972_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v___x_2011_);
lean_ctor_set(v___x_1989_, 3, v___y_2007_);
lean_ctor_set(v___x_1989_, 2, v_v_1994_);
lean_ctor_set(v___x_1989_, 1, v_k_1993_);
lean_ctor_set(v___x_1989_, 0, v___x_2004_);
v___x_2013_ = v___x_1989_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1994_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v___y_2007_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_nat_add(v___x_2016_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec(v___x_2016_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_l_1995_);
lean_ctor_set(v___x_1484_, 3, v_l_1978_);
lean_ctor_set(v___x_1484_, 2, v_v_1977_);
lean_ctor_set(v___x_1484_, 1, v_k_1976_);
lean_ctor_set(v___x_1484_, 0, v___x_2019_);
v___x_2021_ = v___x_1484_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1976_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1977_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1978_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_l_1995_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_nat_add(v___x_1973_, v_size_1974_);
lean_dec(v_size_1974_);
if (lean_obj_tag(v_r_1996_) == 0)
{
lean_object* v_size_2023_; 
v_size_2023_ = lean_ctor_get(v_r_1996_, 0);
lean_inc(v_size_2023_);
v___y_2006_ = v___x_2022_;
v___y_2007_ = v___x_2021_;
v___y_2008_ = v_size_2023_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_unsigned_to_nat(0u);
v___y_2006_ = v___x_2022_;
v___y_2007_ = v___x_2021_;
v___y_2008_ = v___x_2024_;
goto v___jp_2005_;
}
}
}
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_del_object(v___x_1484_);
v___x_2034_ = lean_nat_add(v___x_1973_, v_size_1975_);
lean_dec(v_size_1975_);
v___x_2035_ = lean_nat_add(v___x_2034_, v_size_1974_);
lean_dec(v___x_2034_);
v___x_2036_ = lean_nat_add(v___x_1973_, v_size_1974_);
lean_dec(v_size_1974_);
v___x_2037_ = lean_nat_add(v___x_2036_, v_size_1992_);
lean_dec(v___x_2036_);
lean_inc_ref(v_impl_1972_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v_impl_1972_);
lean_ctor_set(v___x_1989_, 3, v_r_1979_);
lean_ctor_set(v___x_1989_, 2, v_v_1480_);
lean_ctor_set(v___x_1989_, 1, v_k_1479_);
lean_ctor_set(v___x_1989_, 0, v___x_2037_);
v___x_2039_ = v___x_1989_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_r_1979_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_impl_1972_);
v___x_2039_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v_impl_1972_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; 
v_unused_2047_ = lean_ctor_get(v_impl_1972_, 4);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_impl_1972_, 3);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_impl_1972_, 2);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_impl_1972_, 1);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_impl_1972_, 0);
lean_dec(v_unused_2051_);
v___x_2041_ = v_impl_1972_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v_impl_1972_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 4, v___x_2039_);
lean_ctor_set(v___x_2041_, 3, v_l_1978_);
lean_ctor_set(v___x_2041_, 2, v_v_1977_);
lean_ctor_set(v___x_2041_, 1, v_k_1976_);
lean_ctor_set(v___x_2041_, 0, v___x_2035_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_k_1976_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_1977_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_l_1978_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v___x_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v_size_2059_ = lean_ctor_get(v_impl_1972_, 0);
lean_inc(v_size_2059_);
v___x_2060_ = lean_nat_add(v___x_1973_, v_size_2059_);
lean_dec(v_size_2059_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_impl_1972_);
lean_ctor_set(v___x_1484_, 0, v___x_2060_);
v___x_2062_ = v___x_1484_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_impl_1972_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
if (lean_obj_tag(v_l_1481_) == 0)
{
lean_object* v_l_2064_; 
v_l_2064_ = lean_ctor_get(v_l_1481_, 3);
if (lean_obj_tag(v_l_2064_) == 0)
{
lean_object* v_r_2065_; 
lean_inc_ref(v_l_2064_);
v_r_2065_ = lean_ctor_get(v_l_1481_, 4);
lean_inc(v_r_2065_);
if (lean_obj_tag(v_r_2065_) == 0)
{
lean_object* v_size_2066_; lean_object* v_k_2067_; lean_object* v_v_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2081_; 
v_size_2066_ = lean_ctor_get(v_l_1481_, 0);
v_k_2067_ = lean_ctor_get(v_l_1481_, 1);
v_v_2068_ = lean_ctor_get(v_l_1481_, 2);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2082_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_2083_);
v___x_2070_ = v_l_1481_;
v_isShared_2071_ = v_isSharedCheck_2081_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_v_2068_);
lean_inc(v_k_2067_);
lean_inc(v_size_2066_);
lean_dec(v_l_1481_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2081_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_size_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v_size_2072_ = lean_ctor_get(v_r_2065_, 0);
v___x_2073_ = lean_nat_add(v___x_1973_, v_size_2066_);
lean_dec(v_size_2066_);
v___x_2074_ = lean_nat_add(v___x_1973_, v_size_2072_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_impl_1972_);
lean_ctor_set(v___x_2070_, 3, v_r_2065_);
lean_ctor_set(v___x_2070_, 2, v_v_1480_);
lean_ctor_set(v___x_2070_, 1, v_k_1479_);
lean_ctor_set(v___x_2070_, 0, v___x_2074_);
v___x_2076_ = v___x_2070_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2080_, 3, v_r_2065_);
lean_ctor_set(v_reuseFailAlloc_2080_, 4, v_impl_1972_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_2076_);
lean_ctor_set(v___x_1484_, 3, v_l_2064_);
lean_ctor_set(v___x_1484_, 2, v_v_2068_);
lean_ctor_set(v___x_1484_, 1, v_k_2067_);
lean_ctor_set(v___x_1484_, 0, v___x_2073_);
v___x_2078_ = v___x_1484_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_2067_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2096_; 
v_k_2084_ = lean_ctor_get(v_l_1481_, 1);
v_v_2085_ = lean_ctor_get(v_l_1481_, 2);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2097_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_2099_);
v___x_2087_ = v_l_1481_;
v_isShared_2088_ = v_isSharedCheck_2096_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_l_1481_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2096_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_unsigned_to_nat(3u);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 3, v_r_2065_);
lean_ctor_set(v___x_2087_, 2, v_v_1480_);
lean_ctor_set(v___x_2087_, 1, v_k_1479_);
lean_ctor_set(v___x_2087_, 0, v___x_1973_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_r_2065_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_r_2065_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_2091_);
lean_ctor_set(v___x_1484_, 3, v_l_2064_);
lean_ctor_set(v___x_1484_, 2, v_v_2085_);
lean_ctor_set(v___x_1484_, 1, v_k_2084_);
lean_ctor_set(v___x_1484_, 0, v___x_2089_);
v___x_2093_ = v___x_1484_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v_r_2100_; 
v_r_2100_ = lean_ctor_get(v_l_1481_, 4);
lean_inc(v_r_2100_);
if (lean_obj_tag(v_r_2100_) == 0)
{
lean_object* v_k_2101_; lean_object* v_v_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2125_; 
lean_inc(v_l_2064_);
v_k_2101_ = lean_ctor_get(v_l_1481_, 1);
v_v_2102_ = lean_ctor_get(v_l_1481_, 2);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_l_1481_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2126_ = lean_ctor_get(v_l_1481_, 4);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_l_1481_, 3);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_l_1481_, 0);
lean_dec(v_unused_2128_);
v___x_2104_ = v_l_1481_;
v_isShared_2105_ = v_isSharedCheck_2125_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
lean_dec(v_l_1481_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2125_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_k_2106_; lean_object* v_v_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2121_; 
v_k_2106_ = lean_ctor_get(v_r_2100_, 1);
v_v_2107_ = lean_ctor_get(v_r_2100_, 2);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_r_2100_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; 
v_unused_2122_ = lean_ctor_get(v_r_2100_, 4);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_r_2100_, 3);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_r_2100_, 0);
lean_dec(v_unused_2124_);
v___x_2109_ = v_r_2100_;
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_v_2107_);
lean_inc(v_k_2106_);
lean_dec(v_r_2100_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2121_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_unsigned_to_nat(3u);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 4, v_l_2064_);
lean_ctor_set(v___x_2109_, 3, v_l_2064_);
lean_ctor_set(v___x_2109_, 2, v_v_2102_);
lean_ctor_set(v___x_2109_, 1, v_k_2101_);
lean_ctor_set(v___x_2109_, 0, v___x_1973_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_l_2064_);
v___x_2113_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 4, v_l_2064_);
lean_ctor_set(v___x_2104_, 2, v_v_1480_);
lean_ctor_set(v___x_2104_, 1, v_k_1479_);
lean_ctor_set(v___x_2104_, 0, v___x_1973_);
v___x_2115_ = v___x_2104_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_l_2064_);
v___x_2115_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v___x_2115_);
lean_ctor_set(v___x_1484_, 3, v___x_2113_);
lean_ctor_set(v___x_1484_, 2, v_v_2107_);
lean_ctor_set(v___x_1484_, 1, v_k_2106_);
lean_ctor_set(v___x_1484_, 0, v___x_2111_);
v___x_2117_ = v___x_1484_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2106_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2107_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(2u);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_r_2100_);
lean_ctor_set(v___x_1484_, 0, v___x_2129_);
v___x_2131_ = v___x_1484_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_r_2100_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2134_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 4, v_l_1481_);
lean_ctor_set(v___x_1484_, 0, v___x_1973_);
v___x_2134_ = v___x_1484_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_l_1481_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_l_1481_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
}
else
{
return v_t_1478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_2138_, lean_object* v_t_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2138_, v_t_2139_);
lean_dec_ref(v_k_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object* v_val_2141_, lean_object* v_s_2142_){
_start:
{
lean_object* v_toRingState_2143_; lean_object* v_denoteEntries_2144_; lean_object* v_nextId_2145_; lean_object* v_steps_2146_; lean_object* v_queue_2147_; lean_object* v_basis_2148_; lean_object* v_diseqs_2149_; uint8_t v_recheck_2150_; lean_object* v_invSet_2151_; lean_object* v_powIdentityVarCount_2152_; lean_object* v_numEq0_x3f_2153_; uint8_t v_numEq0Updated_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2162_; 
v_toRingState_2143_ = lean_ctor_get(v_s_2142_, 0);
v_denoteEntries_2144_ = lean_ctor_get(v_s_2142_, 1);
v_nextId_2145_ = lean_ctor_get(v_s_2142_, 2);
v_steps_2146_ = lean_ctor_get(v_s_2142_, 3);
v_queue_2147_ = lean_ctor_get(v_s_2142_, 4);
v_basis_2148_ = lean_ctor_get(v_s_2142_, 5);
v_diseqs_2149_ = lean_ctor_get(v_s_2142_, 6);
v_recheck_2150_ = lean_ctor_get_uint8(v_s_2142_, sizeof(void*)*10);
v_invSet_2151_ = lean_ctor_get(v_s_2142_, 7);
v_powIdentityVarCount_2152_ = lean_ctor_get(v_s_2142_, 8);
v_numEq0_x3f_2153_ = lean_ctor_get(v_s_2142_, 9);
v_numEq0Updated_2154_ = lean_ctor_get_uint8(v_s_2142_, sizeof(void*)*10 + 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_s_2142_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2156_ = v_s_2142_;
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_numEq0_x3f_2153_);
lean_inc(v_powIdentityVarCount_2152_);
lean_inc(v_invSet_2151_);
lean_inc(v_diseqs_2149_);
lean_inc(v_basis_2148_);
lean_inc(v_queue_2147_);
lean_inc(v_steps_2146_);
lean_inc(v_nextId_2145_);
lean_inc(v_denoteEntries_2144_);
lean_inc(v_toRingState_2143_);
lean_dec(v_s_2142_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_2141_, v_queue_2147_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 4, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_toRingState_2143_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_denoteEntries_2144_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_nextId_2145_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_steps_2146_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 5, v_basis_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 6, v_diseqs_2149_);
lean_ctor_set(v_reuseFailAlloc_2161_, 7, v_invSet_2151_);
lean_ctor_set(v_reuseFailAlloc_2161_, 8, v_powIdentityVarCount_2152_);
lean_ctor_set(v_reuseFailAlloc_2161_, 9, v_numEq0_x3f_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*10, v_recheck_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*10 + 1, v_numEq0Updated_2154_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object* v_val_2163_, lean_object* v_s_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(v_val_2163_, v_s_2164_);
lean_dec_ref(v_val_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2210_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2210_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2210_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_queue_2175_; lean_object* v___x_2176_; 
v_queue_2175_ = lean_ctor_get(v_a_2171_, 4);
lean_inc(v_queue_2175_);
lean_dec(v_a_2171_);
v___x_2176_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_2175_);
lean_dec(v_queue_2175_);
if (lean_obj_tag(v___x_2176_) == 1)
{
lean_object* v_val_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; 
lean_del_object(v___x_2173_);
v_val_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_val_2177_);
v___f_2178_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2178_, 0, v_val_2177_);
v___x_2179_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2178_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec_ref_known(v___x_2179_, 1);
v___x_2180_ = lean_unsigned_to_nat(1u);
v___x_2181_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2180_, v_a_2167_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2181_, 0);
lean_dec(v_unused_2189_);
v___x_2183_ = v___x_2181_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v___x_2181_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2176_);
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2176_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref_known(v___x_2176_, 1);
v_a_2190_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2181_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2181_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref_known(v___x_2176_, 1);
v_a_2198_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2179_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2179_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_dec(v___x_2176_);
v___x_2206_ = lean_box(0);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2206_);
v___x_2208_ = v___x_2173_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2170_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2170_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2224_, v_a_2225_, v_a_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2250_, lean_object* v_k_2251_, lean_object* v_t_2252_, lean_object* v_h_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2251_, v_t_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2255_, lean_object* v_k_2256_, lean_object* v_t_2257_, lean_object* v_h_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2255_, v_k_2256_, v_t_2257_, v_h_2258_);
lean_dec_ref(v_k_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v_ks_2264_; lean_object* v_vs_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2291_; 
v_ks_2264_ = lean_ctor_get(v_x_2260_, 0);
v_vs_2265_ = lean_ctor_get(v_x_2260_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2267_ = v_x_2260_;
v_isShared_2268_ = v_isSharedCheck_2291_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_vs_2265_);
lean_inc(v_ks_2264_);
lean_dec(v_x_2260_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2291_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_array_get_size(v_ks_2264_);
v___x_2270_ = lean_nat_dec_lt(v_x_2261_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_x_2261_);
v___x_2271_ = lean_array_push(v_ks_2264_, v_x_2262_);
v___x_2272_ = lean_array_push(v_vs_2265_, v_x_2263_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2272_);
lean_ctor_set(v___x_2267_, 0, v___x_2271_);
v___x_2274_ = v___x_2267_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
else
{
lean_object* v_k_x27_2276_; size_t v___x_2277_; size_t v___x_2278_; uint8_t v___x_2279_; 
v_k_x27_2276_ = lean_array_fget_borrowed(v_ks_2264_, v_x_2261_);
v___x_2277_ = lean_ptr_addr(v_x_2262_);
v___x_2278_ = lean_ptr_addr(v_k_x27_2276_);
v___x_2279_ = lean_usize_dec_eq(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2281_; 
if (v_isShared_2268_ == 0)
{
v___x_2281_ = v___x_2267_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_ks_2264_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_vs_2265_);
v___x_2281_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_nat_add(v_x_2261_, v___x_2282_);
lean_dec(v_x_2261_);
v_x_2260_ = v___x_2281_;
v_x_2261_ = v___x_2283_;
goto _start;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2286_ = lean_array_fset(v_ks_2264_, v_x_2261_, v_x_2262_);
v___x_2287_ = lean_array_fset(v_vs_2265_, v_x_2261_, v_x_2263_);
lean_dec(v_x_2261_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2287_);
lean_ctor_set(v___x_2267_, 0, v___x_2286_);
v___x_2289_ = v___x_2267_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2292_, lean_object* v_k_2293_, lean_object* v_v_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2292_, v___x_2295_, v_k_2293_, v_v_2294_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2298_, size_t v_x_2299_, size_t v_x_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
if (lean_obj_tag(v_x_2298_) == 0)
{
lean_object* v_es_2303_; size_t v___x_2304_; size_t v___x_2305_; lean_object* v_j_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_es_2303_ = lean_ctor_get(v_x_2298_, 0);
v___x_2304_ = ((size_t)31ULL);
v___x_2305_ = lean_usize_land(v_x_2299_, v___x_2304_);
v_j_2306_ = lean_usize_to_nat(v___x_2305_);
v___x_2307_ = lean_array_get_size(v_es_2303_);
v___x_2308_ = lean_nat_dec_lt(v_j_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_j_2306_);
lean_dec(v_x_2302_);
lean_dec_ref(v_x_2301_);
return v_x_2298_;
}
else
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2349_; 
lean_inc_ref(v_es_2303_);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_x_2298_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v_x_2298_, 0);
lean_dec(v_unused_2350_);
v___x_2310_ = v_x_2298_;
v_isShared_2311_ = v_isSharedCheck_2349_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_x_2298_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2349_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_v_2312_; lean_object* v___x_2313_; lean_object* v_xs_x27_2314_; lean_object* v___y_2316_; 
v_v_2312_ = lean_array_fget(v_es_2303_, v_j_2306_);
v___x_2313_ = lean_box(0);
v_xs_x27_2314_ = lean_array_fset(v_es_2303_, v_j_2306_, v___x_2313_);
switch(lean_obj_tag(v_v_2312_))
{
case 0:
{
lean_object* v_key_2321_; lean_object* v_val_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2334_; 
v_key_2321_ = lean_ctor_get(v_v_2312_, 0);
v_val_2322_ = lean_ctor_get(v_v_2312_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_v_2312_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2324_ = v_v_2312_;
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_val_2322_);
lean_inc(v_key_2321_);
lean_dec(v_v_2312_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
size_t v___x_2326_; size_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = lean_ptr_addr(v_x_2301_);
v___x_2327_ = lean_ptr_addr(v_key_2321_);
v___x_2328_ = lean_usize_dec_eq(v___x_2326_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_del_object(v___x_2324_);
v___x_2329_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2321_, v_val_2322_, v_x_2301_, v_x_2302_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
v___y_2316_ = v___x_2330_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2332_; 
lean_dec(v_val_2322_);
lean_dec(v_key_2321_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v_x_2302_);
lean_ctor_set(v___x_2324_, 0, v_x_2301_);
v___x_2332_ = v___x_2324_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_x_2301_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_x_2302_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
v___y_2316_ = v___x_2332_;
goto v___jp_2315_;
}
}
}
}
case 1:
{
lean_object* v_node_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2347_; 
v_node_2335_ = lean_ctor_get(v_v_2312_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_v_2312_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2337_ = v_v_2312_;
v_isShared_2338_ = v_isSharedCheck_2347_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_node_2335_);
lean_dec(v_v_2312_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2347_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
size_t v___x_2339_; size_t v___x_2340_; size_t v___x_2341_; size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2339_ = ((size_t)5ULL);
v___x_2340_ = lean_usize_shift_right(v_x_2299_, v___x_2339_);
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_x_2300_, v___x_2341_);
v___x_2343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2335_, v___x_2340_, v___x_2342_, v_x_2301_, v_x_2302_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2343_);
v___x_2345_ = v___x_2337_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v___y_2316_ = v___x_2345_;
goto v___jp_2315_;
}
}
}
default: 
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_x_2301_);
lean_ctor_set(v___x_2348_, 1, v_x_2302_);
v___y_2316_ = v___x_2348_;
goto v___jp_2315_;
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_array_fset(v_xs_x27_2314_, v_j_2306_, v___y_2316_);
lean_dec(v_j_2306_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2317_);
v___x_2319_ = v___x_2310_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
else
{
lean_object* v_ks_2351_; lean_object* v_vs_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2370_; 
v_ks_2351_ = lean_ctor_get(v_x_2298_, 0);
v_vs_2352_ = lean_ctor_get(v_x_2298_, 1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_x_2298_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2354_ = v_x_2298_;
v_isShared_2355_ = v_isSharedCheck_2370_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_vs_2352_);
lean_inc(v_ks_2351_);
lean_dec(v_x_2298_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2370_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_ks_2351_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_vs_2352_);
v___x_2357_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v_newNode_2358_; size_t v___x_2359_; uint8_t v___x_2360_; 
v_newNode_2358_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2357_, v_x_2301_, v_x_2302_);
v___x_2359_ = ((size_t)7ULL);
v___x_2360_ = lean_usize_dec_le(v___x_2359_, v_x_2300_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2358_);
v___x_2362_ = lean_unsigned_to_nat(4u);
v___x_2363_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
lean_dec(v___x_2361_);
if (v___x_2363_ == 0)
{
lean_object* v_ks_2364_; lean_object* v_vs_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_ks_2364_ = lean_ctor_get(v_newNode_2358_, 0);
lean_inc_ref(v_ks_2364_);
v_vs_2365_ = lean_ctor_get(v_newNode_2358_, 1);
lean_inc_ref(v_vs_2365_);
lean_dec_ref(v_newNode_2358_);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2300_, v_ks_2364_, v_vs_2365_, v___x_2366_, v___x_2367_);
lean_dec_ref(v_vs_2365_);
lean_dec_ref(v_ks_2364_);
return v___x_2368_;
}
else
{
return v_newNode_2358_;
}
}
else
{
return v_newNode_2358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2371_, lean_object* v_keys_2372_, lean_object* v_vals_2373_, lean_object* v_i_2374_, lean_object* v_entries_2375_){
_start:
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = lean_array_get_size(v_keys_2372_);
v___x_2377_ = lean_nat_dec_lt(v_i_2374_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_dec(v_i_2374_);
return v_entries_2375_;
}
else
{
lean_object* v_k_2378_; lean_object* v_v_2379_; size_t v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; uint64_t v___x_2383_; size_t v_h_2384_; size_t v___x_2385_; lean_object* v___x_2386_; size_t v___x_2387_; size_t v___x_2388_; size_t v___x_2389_; size_t v_h_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_k_2378_ = lean_array_fget_borrowed(v_keys_2372_, v_i_2374_);
v_v_2379_ = lean_array_fget_borrowed(v_vals_2373_, v_i_2374_);
v___x_2380_ = lean_ptr_addr(v_k_2378_);
v___x_2381_ = ((size_t)3ULL);
v___x_2382_ = lean_usize_shift_right(v___x_2380_, v___x_2381_);
v___x_2383_ = lean_usize_to_uint64(v___x_2382_);
v_h_2384_ = lean_uint64_to_usize(v___x_2383_);
v___x_2385_ = ((size_t)5ULL);
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = ((size_t)1ULL);
v___x_2388_ = lean_usize_sub(v_depth_2371_, v___x_2387_);
v___x_2389_ = lean_usize_mul(v___x_2385_, v___x_2388_);
v_h_2390_ = lean_usize_shift_right(v_h_2384_, v___x_2389_);
v___x_2391_ = lean_nat_add(v_i_2374_, v___x_2386_);
lean_dec(v_i_2374_);
lean_inc(v_v_2379_);
lean_inc(v_k_2378_);
v___x_2392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2375_, v_h_2390_, v_depth_2371_, v_k_2378_, v_v_2379_);
v_i_2374_ = v___x_2391_;
v_entries_2375_ = v___x_2392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2394_, lean_object* v_keys_2395_, lean_object* v_vals_2396_, lean_object* v_i_2397_, lean_object* v_entries_2398_){
_start:
{
size_t v_depth_boxed_2399_; lean_object* v_res_2400_; 
v_depth_boxed_2399_ = lean_unbox_usize(v_depth_2394_);
lean_dec(v_depth_2394_);
v_res_2400_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2399_, v_keys_2395_, v_vals_2396_, v_i_2397_, v_entries_2398_);
lean_dec_ref(v_vals_2396_);
lean_dec_ref(v_keys_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_){
_start:
{
size_t v_x_6465__boxed_2406_; size_t v_x_6466__boxed_2407_; lean_object* v_res_2408_; 
v_x_6465__boxed_2406_ = lean_unbox_usize(v_x_2402_);
lean_dec(v_x_2402_);
v_x_6466__boxed_2407_ = lean_unbox_usize(v_x_2403_);
lean_dec(v_x_2403_);
v_res_2408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2401_, v_x_6465__boxed_2406_, v_x_6466__boxed_2407_, v_x_2404_, v_x_2405_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_x_2411_){
_start:
{
size_t v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; uint64_t v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2412_ = lean_ptr_addr(v_x_2410_);
v___x_2413_ = ((size_t)3ULL);
v___x_2414_ = lean_usize_shift_right(v___x_2412_, v___x_2413_);
v___x_2415_ = lean_usize_to_uint64(v___x_2414_);
v___x_2416_ = lean_uint64_to_usize(v___x_2415_);
v___x_2417_ = ((size_t)1ULL);
v___x_2418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2409_, v___x_2416_, v___x_2417_, v_x_2410_, v_x_2411_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2419_, lean_object* v_ringId_2420_, lean_object* v_s_2421_){
_start:
{
lean_object* v_rings_2422_; lean_object* v_exprToRingId_2423_; lean_object* v_semirings_2424_; lean_object* v_exprToSemiringId_2425_; lean_object* v_ncRings_2426_; lean_object* v_exprToNCRingId_2427_; lean_object* v_ncSemirings_2428_; lean_object* v_exprToNCSemiringId_2429_; lean_object* v_steps_2430_; uint8_t v_reportedMaxDegreeIssue_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2439_; 
v_rings_2422_ = lean_ctor_get(v_s_2421_, 0);
v_exprToRingId_2423_ = lean_ctor_get(v_s_2421_, 1);
v_semirings_2424_ = lean_ctor_get(v_s_2421_, 2);
v_exprToSemiringId_2425_ = lean_ctor_get(v_s_2421_, 3);
v_ncRings_2426_ = lean_ctor_get(v_s_2421_, 4);
v_exprToNCRingId_2427_ = lean_ctor_get(v_s_2421_, 5);
v_ncSemirings_2428_ = lean_ctor_get(v_s_2421_, 6);
v_exprToNCSemiringId_2429_ = lean_ctor_get(v_s_2421_, 7);
v_steps_2430_ = lean_ctor_get(v_s_2421_, 8);
v_reportedMaxDegreeIssue_2431_ = lean_ctor_get_uint8(v_s_2421_, sizeof(void*)*9);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_s_2421_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2433_ = v_s_2421_;
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_steps_2430_);
lean_inc(v_exprToNCSemiringId_2429_);
lean_inc(v_ncSemirings_2428_);
lean_inc(v_exprToNCRingId_2427_);
lean_inc(v_ncRings_2426_);
lean_inc(v_exprToSemiringId_2425_);
lean_inc(v_semirings_2424_);
lean_inc(v_exprToRingId_2423_);
lean_inc(v_rings_2422_);
lean_dec(v_s_2421_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2423_, v_e_2419_, v_ringId_2420_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 1, v___x_2435_);
v___x_2437_ = v___x_2433_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_rings_2422_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_semirings_2424_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_exprToSemiringId_2425_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v_ncRings_2426_);
lean_ctor_set(v_reuseFailAlloc_2438_, 5, v_exprToNCRingId_2427_);
lean_ctor_set(v_reuseFailAlloc_2438_, 6, v_ncSemirings_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 7, v_exprToNCSemiringId_2429_);
lean_ctor_set(v_reuseFailAlloc_2438_, 8, v_steps_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2438_, sizeof(void*)*9, v_reportedMaxDegreeIssue_2431_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v_ringId_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; 
v_ringId_2456_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_ringId_2456_);
lean_inc_ref(v_e_2443_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2457_, 0, v_e_2443_);
lean_closure_set(v___f_2457_, 1, v_ringId_2456_);
v___x_2458_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2443_, v_a_2445_, v_a_2450_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
if (lean_obj_tag(v_a_2459_) == 1)
{
lean_object* v_val_2460_; uint8_t v___x_2461_; 
lean_dec_ref(v___f_2457_);
v_val_2460_ = lean_ctor_get(v_a_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_a_2459_, 1);
v___x_2461_ = lean_nat_dec_eq(v_val_2460_, v_ringId_2456_);
lean_dec(v_val_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2463_ = l_Lean_indentExpr(v_e_2443_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2446_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; uint8_t v_verbose_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v_verbose_2467_ = lean_ctor_get_uint8(v_a_2466_, 0);
lean_dec(v_a_2466_);
if (v_verbose_2467_ == 0)
{
lean_dec_ref_known(v___x_2464_, 2);
goto v___jp_2453_;
}
else
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Meta_Sym_reportIssue(v___x_2464_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_dec_ref_known(v___x_2468_, 1);
goto v___jp_2453_;
}
else
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref_known(v___x_2464_, 2);
v_a_2469_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2465_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2465_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_dec_ref(v_e_2443_);
goto v___jp_2453_;
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_dec(v_a_2459_);
lean_dec_ref(v_e_2443_);
v___x_2477_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2477_, v___f_2457_, v_a_2445_);
return v___x_2478_;
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v___f_2457_);
lean_dec_ref(v_e_2443_);
v_a_2479_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2458_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2458_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
v___jp_2453_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2498_, v_a_2499_, v_a_2500_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2527_, v_x_2528_, v_x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2531_, lean_object* v_x_2532_, size_t v_x_2533_, size_t v_x_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2532_, v_x_2533_, v_x_2534_, v_x_2535_, v_x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
size_t v_x_6751__boxed_2544_; size_t v_x_6752__boxed_2545_; lean_object* v_res_2546_; 
v_x_6751__boxed_2544_ = lean_unbox_usize(v_x_2540_);
lean_dec(v_x_2540_);
v_x_6752__boxed_2545_ = lean_unbox_usize(v_x_2541_);
lean_dec(v_x_2541_);
v_res_2546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2538_, v_x_2539_, v_x_6751__boxed_2544_, v_x_6752__boxed_2545_, v_x_2542_, v_x_2543_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2547_, lean_object* v_n_2548_, lean_object* v_k_2549_, lean_object* v_v_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2548_, v_k_2549_, v_v_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2552_, size_t v_depth_2553_, lean_object* v_keys_2554_, lean_object* v_vals_2555_, lean_object* v_heq_2556_, lean_object* v_i_2557_, lean_object* v_entries_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2553_, v_keys_2554_, v_vals_2555_, v_i_2557_, v_entries_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2560_, lean_object* v_depth_2561_, lean_object* v_keys_2562_, lean_object* v_vals_2563_, lean_object* v_heq_2564_, lean_object* v_i_2565_, lean_object* v_entries_2566_){
_start:
{
size_t v_depth_boxed_2567_; lean_object* v_res_2568_; 
v_depth_boxed_2567_ = lean_unbox_usize(v_depth_2561_);
lean_dec(v_depth_2561_);
v_res_2568_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2560_, v_depth_boxed_2567_, v_keys_2562_, v_vals_2563_, v_heq_2564_, v_i_2565_, v_entries_2566_);
lean_dec_ref(v_vals_2563_);
lean_dec_ref(v_keys_2562_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2570_, v_x_2571_, v_x_2572_, v_x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2575_, lean_object* v___f_2576_, lean_object* v___f_2577_, lean_object* v_size_2578_, lean_object* v_s_2579_){
_start:
{
lean_object* v_vars_2580_; lean_object* v_varMap_2581_; lean_object* v_denote_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
v_vars_2580_ = lean_ctor_get(v_s_2579_, 0);
v_varMap_2581_ = lean_ctor_get(v_s_2579_, 1);
v_denote_2582_ = lean_ctor_get(v_s_2579_, 2);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_s_2579_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v_s_2579_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_denote_2582_);
lean_inc(v_varMap_2581_);
lean_inc(v_vars_2580_);
lean_dec(v_s_2579_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_inc_ref(v_e_2575_);
v___x_2586_ = l_Lean_PersistentArray_push___redArg(v_vars_2580_, v_e_2575_);
v___x_2587_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2576_, v___f_2577_, v_varMap_2581_, v_e_2575_, v_size_2578_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___x_2587_);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_denote_2582_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2592_, lean_object* v_size_2593_, lean_object* v_____r_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_apply_2(v_toPure_2592_, lean_box(0), v_size_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2596_, lean_object* v_inst_2597_, lean_object* v_toBind_2598_, lean_object* v___f_2599_, lean_object* v_____r_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2601_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2602_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2602_, 0, lean_box(0));
lean_closure_set(v___x_2602_, 1, v___x_2601_);
lean_closure_set(v___x_2602_, 2, v_e_2596_);
v___x_2603_ = lean_apply_2(v_inst_2597_, lean_box(0), v___x_2602_);
v___x_2604_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2603_, v___f_2599_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2605_, lean_object* v_e_2606_, lean_object* v_toBind_2607_, lean_object* v___f_2608_, lean_object* v_____r_2609_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_apply_1(v_inst_2605_, v_e_2606_);
v___x_2611_ = lean_apply_4(v_toBind_2607_, lean_box(0), lean_box(0), v___x_2610_, v___f_2608_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2612_, lean_object* v___f_2613_, lean_object* v_e_2614_, lean_object* v_toPure_2615_, lean_object* v_inst_2616_, lean_object* v_toBind_2617_, lean_object* v_inst_2618_, lean_object* v_modifyRingState_2619_, lean_object* v_s_2620_){
_start:
{
lean_object* v_vars_2621_; lean_object* v_varMap_2622_; lean_object* v___x_2623_; 
v_vars_2621_ = lean_ctor_get(v_s_2620_, 0);
lean_inc_ref(v_vars_2621_);
v_varMap_2622_ = lean_ctor_get(v_s_2620_, 1);
lean_inc_ref(v_varMap_2622_);
lean_dec_ref(v_s_2620_);
lean_inc_ref(v_e_2614_);
lean_inc_ref(v___f_2613_);
lean_inc_ref(v___f_2612_);
v___x_2623_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2612_, v___f_2613_, v_varMap_2622_, v_e_2614_);
lean_dec_ref(v_varMap_2622_);
if (lean_obj_tag(v___x_2623_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v_vars_2621_);
lean_dec(v_modifyRingState_2619_);
lean_dec(v_inst_2618_);
lean_dec(v_toBind_2617_);
lean_dec(v_inst_2616_);
lean_dec_ref(v_e_2614_);
lean_dec_ref(v___f_2613_);
lean_dec_ref(v___f_2612_);
v_val_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_val_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = lean_apply_2(v_toPure_2615_, lean_box(0), v_val_2624_);
return v___x_2625_;
}
else
{
lean_object* v_size_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v___x_2623_);
v_size_2626_ = lean_ctor_get(v_vars_2621_, 2);
lean_inc_n(v_size_2626_, 2);
lean_dec_ref(v_vars_2621_);
lean_inc_ref_n(v_e_2614_, 2);
v___f_2627_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2627_, 0, v_e_2614_);
lean_closure_set(v___f_2627_, 1, v___f_2612_);
lean_closure_set(v___f_2627_, 2, v___f_2613_);
lean_closure_set(v___f_2627_, 3, v_size_2626_);
v___f_2628_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2628_, 0, v_toPure_2615_);
lean_closure_set(v___f_2628_, 1, v_size_2626_);
lean_inc_n(v_toBind_2617_, 2);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2629_, 0, v_e_2614_);
lean_closure_set(v___f_2629_, 1, v_inst_2616_);
lean_closure_set(v___f_2629_, 2, v_toBind_2617_);
lean_closure_set(v___f_2629_, 3, v___f_2628_);
v___f_2630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2630_, 0, v_inst_2618_);
lean_closure_set(v___f_2630_, 1, v_e_2614_);
lean_closure_set(v___f_2630_, 2, v_toBind_2617_);
lean_closure_set(v___f_2630_, 3, v___f_2629_);
v___x_2631_ = lean_apply_1(v_modifyRingState_2619_, v___f_2627_);
v___x_2632_ = lean_apply_4(v_toBind_2617_, lean_box(0), lean_box(0), v___x_2631_, v___f_2630_);
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_e_2639_){
_start:
{
lean_object* v_toApplicative_2640_; lean_object* v_toBind_2641_; lean_object* v_getRingState_2642_; lean_object* v_modifyRingState_2643_; lean_object* v_toPure_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; 
v_toApplicative_2640_ = lean_ctor_get(v_inst_2636_, 0);
lean_inc_ref(v_toApplicative_2640_);
v_toBind_2641_ = lean_ctor_get(v_inst_2636_, 1);
lean_inc_n(v_toBind_2641_, 2);
lean_dec_ref(v_inst_2636_);
v_getRingState_2642_ = lean_ctor_get(v_inst_2637_, 0);
lean_inc(v_getRingState_2642_);
v_modifyRingState_2643_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc(v_modifyRingState_2643_);
lean_dec_ref(v_inst_2637_);
v_toPure_2644_ = lean_ctor_get(v_toApplicative_2640_, 1);
lean_inc(v_toPure_2644_);
lean_dec_ref(v_toApplicative_2640_);
v___f_2645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2647_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2647_, 0, v___f_2645_);
lean_closure_set(v___f_2647_, 1, v___f_2646_);
lean_closure_set(v___f_2647_, 2, v_e_2639_);
lean_closure_set(v___f_2647_, 3, v_toPure_2644_);
lean_closure_set(v___f_2647_, 4, v_inst_2635_);
lean_closure_set(v___f_2647_, 5, v_toBind_2641_);
lean_closure_set(v___f_2647_, 6, v_inst_2638_);
lean_closure_set(v___f_2647_, 7, v_modifyRingState_2643_);
v___x_2648_ = lean_apply_4(v_toBind_2641_, lean_box(0), lean_box(0), v_getRingState_2642_, v___f_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_e_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2650_, v_inst_2651_, v_inst_2652_, v_inst_2653_, v_e_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2656_, v___y_2657_, v___y_2658_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object* v___f_2686_, lean_object* v___x_2687_, lean_object* v___x_2688_, lean_object* v___f_2689_, lean_object* v_e_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2690_, v___y_2692_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; uint8_t v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
if (v___x_2705_ == 0)
{
lean_object* v_gen_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_gen_2706_ = lean_ctor_get(v___y_2691_, 1);
v___x_2707_ = lean_box(0);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc(v_gen_2706_);
lean_inc_ref(v_e_2690_);
v___x_2708_ = lean_grind_internalize(v_e_2690_, v_gen_2706_, v___x_2707_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v___x_3338__overap_2709_; lean_object* v___x_2710_; 
lean_dec_ref_known(v___x_2708_, 1);
v___x_3338__overap_2709_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2686_, v___x_2687_, v___x_2688_, v___f_2689_, v_e_2690_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
v___x_2710_ = lean_apply_12(v___x_3338__overap_2709_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, lean_box(0));
return v___x_2710_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_e_2690_);
lean_dec_ref(v___f_2689_);
lean_dec_ref(v___x_2688_);
lean_dec_ref(v___x_2687_);
lean_dec(v___f_2686_);
v_a_2711_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2708_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2708_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v___x_3342__overap_2719_; lean_object* v___x_2720_; 
v___x_3342__overap_2719_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2686_, v___x_2687_, v___x_2688_, v___f_2689_, v_e_2690_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
v___x_2720_ = lean_apply_12(v___x_3342__overap_2719_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, lean_box(0));
return v___x_2720_;
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_e_2690_);
lean_dec_ref(v___f_2689_);
lean_dec_ref(v___x_2688_);
lean_dec_ref(v___x_2687_);
lean_dec(v___f_2686_);
v_a_2721_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2703_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2703_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object** _args){
lean_object* v___f_2729_ = _args[0];
lean_object* v___x_2730_ = _args[1];
lean_object* v___x_2731_ = _args[2];
lean_object* v___f_2732_ = _args[3];
lean_object* v_e_2733_ = _args[4];
lean_object* v___y_2734_ = _args[5];
lean_object* v___y_2735_ = _args[6];
lean_object* v___y_2736_ = _args[7];
lean_object* v___y_2737_ = _args[8];
lean_object* v___y_2738_ = _args[9];
lean_object* v___y_2739_ = _args[10];
lean_object* v___y_2740_ = _args[11];
lean_object* v___y_2741_ = _args[12];
lean_object* v___y_2742_ = _args[13];
lean_object* v___y_2743_ = _args[14];
lean_object* v___y_2744_ = _args[15];
lean_object* v___y_2745_ = _args[16];
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___f_2729_, v___x_2730_, v___x_2731_, v___f_2732_, v_e_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2746_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0(void){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_instMonadEIO___redArg();
return v___x_2747_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0);
v___x_2749_ = l_StateRefT_x27_instMonad___redArg(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM(void){
_start:
{
lean_object* v___x_2759_; lean_object* v_toApplicative_2760_; lean_object* v_toFunctor_2761_; lean_object* v_toSeq_2762_; lean_object* v_toSeqLeft_2763_; lean_object* v_toSeqRight_2764_; lean_object* v___f_2765_; lean_object* v___f_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___f_2771_; lean_object* v___f_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v_toApplicative_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2823_; 
v___x_2759_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1);
v_toApplicative_2760_ = lean_ctor_get(v___x_2759_, 0);
v_toFunctor_2761_ = lean_ctor_get(v_toApplicative_2760_, 0);
v_toSeq_2762_ = lean_ctor_get(v_toApplicative_2760_, 2);
v_toSeqLeft_2763_ = lean_ctor_get(v_toApplicative_2760_, 3);
v_toSeqRight_2764_ = lean_ctor_get(v_toApplicative_2760_, 4);
v___f_2765_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2));
v___f_2766_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3));
lean_inc_ref_n(v_toFunctor_2761_, 2);
v___f_2767_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2767_, 0, v_toFunctor_2761_);
v___f_2768_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2768_, 0, v_toFunctor_2761_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___f_2767_);
lean_ctor_set(v___x_2769_, 1, v___f_2768_);
lean_inc(v_toSeqRight_2764_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toSeqRight_2764_);
lean_inc(v_toSeqLeft_2763_);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2771_, 0, v_toSeqLeft_2763_);
lean_inc(v_toSeq_2762_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeq_2762_);
v___x_2773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2769_);
lean_ctor_set(v___x_2773_, 1, v___f_2765_);
lean_ctor_set(v___x_2773_, 2, v___f_2772_);
lean_ctor_set(v___x_2773_, 3, v___f_2771_);
lean_ctor_set(v___x_2773_, 4, v___f_2770_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___f_2766_);
v___x_2775_ = l_StateRefT_x27_instMonad___redArg(v___x_2774_);
v_toApplicative_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2775_, 1);
lean_dec(v_unused_2824_);
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2823_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_toApplicative_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2823_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_toFunctor_2780_; lean_object* v_toSeq_2781_; lean_object* v_toSeqLeft_2782_; lean_object* v_toSeqRight_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2821_; 
v_toFunctor_2780_ = lean_ctor_get(v_toApplicative_2776_, 0);
v_toSeq_2781_ = lean_ctor_get(v_toApplicative_2776_, 2);
v_toSeqLeft_2782_ = lean_ctor_get(v_toApplicative_2776_, 3);
v_toSeqRight_2783_ = lean_ctor_get(v_toApplicative_2776_, 4);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_toApplicative_2776_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_toApplicative_2776_, 1);
lean_dec(v_unused_2822_);
v___x_2785_ = v_toApplicative_2776_;
v_isShared_2786_ = v_isSharedCheck_2821_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_toSeqRight_2783_);
lean_inc(v_toSeqLeft_2782_);
lean_inc(v_toSeq_2781_);
lean_inc(v_toFunctor_2780_);
lean_dec(v_toApplicative_2776_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2821_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___f_2787_; lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v___f_2792_; lean_object* v___f_2793_; lean_object* v___f_2794_; lean_object* v___x_2796_; 
v___f_2787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4));
v___f_2788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5));
lean_inc_ref(v_toFunctor_2780_);
v___f_2789_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2789_, 0, v_toFunctor_2780_);
v___f_2790_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2790_, 0, v_toFunctor_2780_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___f_2789_);
lean_ctor_set(v___x_2791_, 1, v___f_2790_);
v___f_2792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2792_, 0, v_toSeqRight_2783_);
v___f_2793_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2793_, 0, v_toSeqLeft_2782_);
v___f_2794_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2794_, 0, v_toSeq_2781_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 4, v___f_2792_);
lean_ctor_set(v___x_2785_, 3, v___f_2793_);
lean_ctor_set(v___x_2785_, 2, v___f_2794_);
lean_ctor_set(v___x_2785_, 1, v___f_2787_);
lean_ctor_set(v___x_2785_, 0, v___x_2791_);
v___x_2796_ = v___x_2785_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___f_2787_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v___f_2794_);
lean_ctor_set(v_reuseFailAlloc_2820_, 3, v___f_2793_);
lean_ctor_set(v_reuseFailAlloc_2820_, 4, v___f_2792_);
v___x_2796_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2798_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 1, v___f_2788_);
lean_ctor_set(v___x_2778_, 0, v___x_2796_);
v___x_2798_ = v___x_2778_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___f_2788_);
v___x_2798_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v_toApplicative_2807_; lean_object* v_toBind_2808_; lean_object* v_getCommRingState_2809_; lean_object* v_modifyCommRingState_2810_; lean_object* v_toPure_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; lean_object* v___f_2818_; 
v___x_2799_ = l_StateRefT_x27_instMonad___redArg(v___x_2798_);
v___x_2800_ = l_ReaderT_instMonad___redArg(v___x_2799_);
v___x_2801_ = l_StateRefT_x27_instMonad___redArg(v___x_2800_);
v___x_2802_ = l_ReaderT_instMonad___redArg(v___x_2801_);
v___x_2803_ = l_ReaderT_instMonad___redArg(v___x_2802_);
v___x_2804_ = l_StateRefT_x27_instMonad___redArg(v___x_2803_);
v___x_2805_ = l_ReaderT_instMonad___redArg(v___x_2804_);
v___x_2806_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
v_toApplicative_2807_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_ref(v_toApplicative_2807_);
v_toBind_2808_ = lean_ctor_get(v___x_2805_, 1);
lean_inc(v_toBind_2808_);
v_getCommRingState_2809_ = lean_ctor_get(v___x_2806_, 0);
v_modifyCommRingState_2810_ = lean_ctor_get(v___x_2806_, 1);
v_toPure_2811_ = lean_ctor_get(v_toApplicative_2807_, 1);
lean_inc(v_toPure_2811_);
lean_dec_ref(v_toApplicative_2807_);
v___f_2812_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8));
lean_inc(v_modifyCommRingState_2810_);
v___f_2813_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2813_, 0, v_modifyCommRingState_2810_);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2814_, 0, v_toPure_2811_);
lean_inc(v_getCommRingState_2809_);
v___x_2815_ = lean_apply_4(v_toBind_2808_, lean_box(0), lean_box(0), v_getCommRingState_2809_, v___f_2814_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___f_2813_);
v___f_2817_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0));
v___f_2818_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed), 17, 4);
lean_closure_set(v___f_2818_, 0, v___f_2812_);
lean_closure_set(v___f_2818_, 1, v___x_2805_);
lean_closure_set(v___f_2818_, 2, v___x_2816_);
lean_closure_set(v___f_2818_, 3, v___f_2817_);
return v___f_2818_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_2825_; lean_object* v_n_2826_; 
v___x_2825_ = lean_unsigned_to_nat(1u);
v_n_2826_ = l_Lean_mkRawNatLit(v___x_2825_);
return v_n_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_u_2840_, lean_object* v_type_2841_, lean_object* v_semiringInst_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_n_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v_ofNatInst_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_n_2850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5));
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_u_2840_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
lean_inc_ref(v___x_2853_);
v___x_2854_ = l_Lean_mkConst(v___x_2851_, v___x_2853_);
lean_inc_ref(v_type_2841_);
v_ofNatInst_2855_ = l_Lean_mkApp3(v___x_2854_, v_type_2841_, v_semiringInst_2842_, v_n_2850_);
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7));
v___x_2857_ = l_Lean_mkConst(v___x_2856_, v___x_2853_);
v___x_2858_ = l_Lean_mkApp3(v___x_2857_, v_type_2841_, v_n_2850_, v_ofNatInst_2855_);
v___x_2859_ = l_Lean_Meta_Sym_canon(v___x_2858_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Meta_Sym_shareCommon(v_a_2860_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2861_;
}
else
{
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object* v_u_2862_, lean_object* v_type_2863_, lean_object* v_semiringInst_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_2862_, v_type_2863_, v_semiringInst_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_u_2873_, lean_object* v_type_2874_, lean_object* v_semiringInst_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_2873_, v_type_2874_, v_semiringInst_2875_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object* v_u_2889_, lean_object* v_type_2890_, lean_object* v_semiringInst_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_2889_, v_type_2890_, v_semiringInst_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object* v_a_2905_, lean_object* v_s_2906_){
_start:
{
lean_object* v_toRing_2907_; lean_object* v_invFn_x3f_2908_; lean_object* v_divFn_x3f_2909_; lean_object* v_semiringId_x3f_2910_; lean_object* v_commSemiringInst_2911_; lean_object* v_commRingInst_2912_; lean_object* v_noZeroDivInst_x3f_2913_; lean_object* v_fieldInst_x3f_2914_; lean_object* v_powIdentityInst_x3f_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2946_; 
v_toRing_2907_ = lean_ctor_get(v_s_2906_, 0);
v_invFn_x3f_2908_ = lean_ctor_get(v_s_2906_, 1);
v_divFn_x3f_2909_ = lean_ctor_get(v_s_2906_, 2);
v_semiringId_x3f_2910_ = lean_ctor_get(v_s_2906_, 3);
v_commSemiringInst_2911_ = lean_ctor_get(v_s_2906_, 4);
v_commRingInst_2912_ = lean_ctor_get(v_s_2906_, 5);
v_noZeroDivInst_x3f_2913_ = lean_ctor_get(v_s_2906_, 6);
v_fieldInst_x3f_2914_ = lean_ctor_get(v_s_2906_, 7);
v_powIdentityInst_x3f_2915_ = lean_ctor_get(v_s_2906_, 8);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_s_2906_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2917_ = v_s_2906_;
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2915_);
lean_inc(v_fieldInst_x3f_2914_);
lean_inc(v_noZeroDivInst_x3f_2913_);
lean_inc(v_commRingInst_2912_);
lean_inc(v_commSemiringInst_2911_);
lean_inc(v_semiringId_x3f_2910_);
lean_inc(v_divFn_x3f_2909_);
lean_inc(v_invFn_x3f_2908_);
lean_inc(v_toRing_2907_);
lean_dec(v_s_2906_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_id_2919_; lean_object* v_type_2920_; lean_object* v_u_2921_; lean_object* v_ringInst_2922_; lean_object* v_semiringInst_2923_; lean_object* v_charInst_x3f_2924_; lean_object* v_addFn_x3f_2925_; lean_object* v_mulFn_x3f_2926_; lean_object* v_subFn_x3f_2927_; lean_object* v_negFn_x3f_2928_; lean_object* v_powFn_x3f_2929_; lean_object* v_intCastFn_x3f_2930_; lean_object* v_natCastFn_x3f_2931_; lean_object* v_natSMulFn_x3f_2932_; lean_object* v_intSMulFn_x3f_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2944_; 
v_id_2919_ = lean_ctor_get(v_toRing_2907_, 0);
v_type_2920_ = lean_ctor_get(v_toRing_2907_, 1);
v_u_2921_ = lean_ctor_get(v_toRing_2907_, 2);
v_ringInst_2922_ = lean_ctor_get(v_toRing_2907_, 3);
v_semiringInst_2923_ = lean_ctor_get(v_toRing_2907_, 4);
v_charInst_x3f_2924_ = lean_ctor_get(v_toRing_2907_, 5);
v_addFn_x3f_2925_ = lean_ctor_get(v_toRing_2907_, 6);
v_mulFn_x3f_2926_ = lean_ctor_get(v_toRing_2907_, 7);
v_subFn_x3f_2927_ = lean_ctor_get(v_toRing_2907_, 8);
v_negFn_x3f_2928_ = lean_ctor_get(v_toRing_2907_, 9);
v_powFn_x3f_2929_ = lean_ctor_get(v_toRing_2907_, 10);
v_intCastFn_x3f_2930_ = lean_ctor_get(v_toRing_2907_, 11);
v_natCastFn_x3f_2931_ = lean_ctor_get(v_toRing_2907_, 12);
v_natSMulFn_x3f_2932_ = lean_ctor_get(v_toRing_2907_, 13);
v_intSMulFn_x3f_2933_ = lean_ctor_get(v_toRing_2907_, 14);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_toRing_2907_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_toRing_2907_, 15);
lean_dec(v_unused_2945_);
v___x_2935_ = v_toRing_2907_;
v_isShared_2936_ = v_isSharedCheck_2944_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_intSMulFn_x3f_2933_);
lean_inc(v_natSMulFn_x3f_2932_);
lean_inc(v_natCastFn_x3f_2931_);
lean_inc(v_intCastFn_x3f_2930_);
lean_inc(v_powFn_x3f_2929_);
lean_inc(v_negFn_x3f_2928_);
lean_inc(v_subFn_x3f_2927_);
lean_inc(v_mulFn_x3f_2926_);
lean_inc(v_addFn_x3f_2925_);
lean_inc(v_charInst_x3f_2924_);
lean_inc(v_semiringInst_2923_);
lean_inc(v_ringInst_2922_);
lean_inc(v_u_2921_);
lean_inc(v_type_2920_);
lean_inc(v_id_2919_);
lean_dec(v_toRing_2907_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2944_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2905_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 15, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_id_2919_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_type_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_u_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_ringInst_2922_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_semiringInst_2923_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_charInst_x3f_2924_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v_addFn_x3f_2925_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v_mulFn_x3f_2926_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v_subFn_x3f_2927_);
lean_ctor_set(v_reuseFailAlloc_2943_, 9, v_negFn_x3f_2928_);
lean_ctor_set(v_reuseFailAlloc_2943_, 10, v_powFn_x3f_2929_);
lean_ctor_set(v_reuseFailAlloc_2943_, 11, v_intCastFn_x3f_2930_);
lean_ctor_set(v_reuseFailAlloc_2943_, 12, v_natCastFn_x3f_2931_);
lean_ctor_set(v_reuseFailAlloc_2943_, 13, v_natSMulFn_x3f_2932_);
lean_ctor_set(v_reuseFailAlloc_2943_, 14, v_intSMulFn_x3f_2933_);
lean_ctor_set(v_reuseFailAlloc_2943_, 15, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2941_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2939_);
v___x_2941_ = v___x_2917_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_invFn_x3f_2908_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_divFn_x3f_2909_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v_semiringId_x3f_2910_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v_commSemiringInst_2911_);
lean_ctor_set(v_reuseFailAlloc_2942_, 5, v_commRingInst_2912_);
lean_ctor_set(v_reuseFailAlloc_2942_, 6, v_noZeroDivInst_x3f_2913_);
lean_ctor_set(v_reuseFailAlloc_2942_, 7, v_fieldInst_x3f_2914_);
lean_ctor_set(v_reuseFailAlloc_2942_, 8, v_powIdentityInst_x3f_2915_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2947_, lean_object* v_i_2948_, lean_object* v_k_2949_){
_start:
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = lean_array_get_size(v_keys_2947_);
v___x_2951_ = lean_nat_dec_lt(v_i_2948_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_dec(v_i_2948_);
return v___x_2951_;
}
else
{
lean_object* v_k_x27_2952_; size_t v___x_2953_; size_t v___x_2954_; uint8_t v___x_2955_; 
v_k_x27_2952_ = lean_array_fget_borrowed(v_keys_2947_, v_i_2948_);
v___x_2953_ = lean_ptr_addr(v_k_2949_);
v___x_2954_ = lean_ptr_addr(v_k_x27_2952_);
v___x_2955_ = lean_usize_dec_eq(v___x_2953_, v___x_2954_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_add(v_i_2948_, v___x_2956_);
lean_dec(v_i_2948_);
v_i_2948_ = v___x_2957_;
goto _start;
}
else
{
lean_dec(v_i_2948_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2959_, lean_object* v_i_2960_, lean_object* v_k_2961_){
_start:
{
uint8_t v_res_2962_; lean_object* v_r_2963_; 
v_res_2962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_2959_, v_i_2960_, v_k_2961_);
lean_dec_ref(v_k_2961_);
lean_dec_ref(v_keys_2959_);
v_r_2963_ = lean_box(v_res_2962_);
return v_r_2963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object* v_x_2964_, size_t v_x_2965_, lean_object* v_x_2966_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v_es_2967_; lean_object* v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; lean_object* v_j_2971_; lean_object* v___x_2972_; 
v_es_2967_ = lean_ctor_get(v_x_2964_, 0);
v___x_2968_ = lean_box(2);
v___x_2969_ = ((size_t)31ULL);
v___x_2970_ = lean_usize_land(v_x_2965_, v___x_2969_);
v_j_2971_ = lean_usize_to_nat(v___x_2970_);
v___x_2972_ = lean_array_get_borrowed(v___x_2968_, v_es_2967_, v_j_2971_);
lean_dec(v_j_2971_);
switch(lean_obj_tag(v___x_2972_))
{
case 0:
{
lean_object* v_key_2973_; size_t v___x_2974_; size_t v___x_2975_; uint8_t v___x_2976_; 
v_key_2973_ = lean_ctor_get(v___x_2972_, 0);
v___x_2974_ = lean_ptr_addr(v_x_2966_);
v___x_2975_ = lean_ptr_addr(v_key_2973_);
v___x_2976_ = lean_usize_dec_eq(v___x_2974_, v___x_2975_);
return v___x_2976_;
}
case 1:
{
lean_object* v_node_2977_; size_t v___x_2978_; size_t v___x_2979_; 
v_node_2977_ = lean_ctor_get(v___x_2972_, 0);
v___x_2978_ = ((size_t)5ULL);
v___x_2979_ = lean_usize_shift_right(v_x_2965_, v___x_2978_);
v_x_2964_ = v_node_2977_;
v_x_2965_ = v___x_2979_;
goto _start;
}
default: 
{
uint8_t v___x_2981_; 
v___x_2981_ = 0;
return v___x_2981_;
}
}
}
else
{
lean_object* v_ks_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_ks_2982_ = lean_ctor_get(v_x_2964_, 0);
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_ks_2982_, v___x_2983_, v_x_2966_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object* v_x_2985_, lean_object* v_x_2986_, lean_object* v_x_2987_){
_start:
{
size_t v_x_9654__boxed_2988_; uint8_t v_res_2989_; lean_object* v_r_2990_; 
v_x_9654__boxed_2988_ = lean_unbox_usize(v_x_2986_);
lean_dec(v_x_2986_);
v_res_2989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_2985_, v_x_9654__boxed_2988_, v_x_2987_);
lean_dec_ref(v_x_2987_);
lean_dec_ref(v_x_2985_);
v_r_2990_ = lean_box(v_res_2989_);
return v_r_2990_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object* v_x_2991_, lean_object* v_x_2992_){
_start:
{
size_t v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; uint64_t v___x_2996_; size_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2993_ = lean_ptr_addr(v_x_2992_);
v___x_2994_ = ((size_t)3ULL);
v___x_2995_ = lean_usize_shift_right(v___x_2993_, v___x_2994_);
v___x_2996_ = lean_usize_to_uint64(v___x_2995_);
v___x_2997_ = lean_uint64_to_usize(v___x_2996_);
v___x_2998_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_2991_, v___x_2997_, v_x_2992_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
uint8_t v_res_3001_; lean_object* v_r_3002_; 
v_res_3001_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_2999_, v_x_3000_);
lean_dec_ref(v_x_3000_);
lean_dec_ref(v_x_2999_);
v_r_3002_ = lean_box(v_res_3001_);
return v_r_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_one_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v_toRing_3069_; lean_object* v_one_x3f_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v_toRing_3069_ = lean_ctor_get(v_a_3068_, 0);
lean_inc_ref(v_toRing_3069_);
lean_dec(v_a_3068_);
v_one_x3f_3070_ = lean_ctor_get(v_toRing_3069_, 15);
if (lean_obj_tag(v_one_x3f_3070_) == 1)
{
lean_object* v_val_3071_; 
lean_inc_ref(v_one_x3f_3070_);
lean_dec_ref(v_toRing_3069_);
v_val_3071_ = lean_ctor_get(v_one_x3f_3070_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v_one_x3f_3070_, 1);
v_one_3016_ = v_val_3071_;
v___y_3017_ = v_a_3003_;
v___y_3018_ = v_a_3004_;
v___y_3019_ = v_a_3005_;
v___y_3020_ = v_a_3006_;
v___y_3021_ = v_a_3007_;
v___y_3022_ = v_a_3008_;
v___y_3023_ = v_a_3009_;
v___y_3024_ = v_a_3010_;
v___y_3025_ = v_a_3011_;
v___y_3026_ = v_a_3012_;
v___y_3027_ = v_a_3013_;
goto v___jp_3015_;
}
else
{
lean_object* v_type_3072_; lean_object* v_u_3073_; lean_object* v_semiringInst_3074_; lean_object* v___x_3075_; 
v_type_3072_ = lean_ctor_get(v_toRing_3069_, 1);
lean_inc_ref(v_type_3072_);
v_u_3073_ = lean_ctor_get(v_toRing_3069_, 2);
lean_inc(v_u_3073_);
v_semiringInst_3074_ = lean_ctor_get(v_toRing_3069_, 4);
lean_inc_ref(v_semiringInst_3074_);
lean_dec_ref(v_toRing_3069_);
v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3073_, v_type_3072_, v_semiringInst_3074_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___f_3077_; lean_object* v___x_3078_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_n(v_a_3076_, 2);
lean_dec_ref_known(v___x_3075_, 1);
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0), 2, 1);
lean_closure_set(v___f_3077_, 0, v_a_3076_);
v___x_3078_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3077_, v_a_3003_, v_a_3009_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref_known(v___x_3078_, 1);
v_one_3016_ = v_a_3076_;
v___y_3017_ = v_a_3003_;
v___y_3018_ = v_a_3004_;
v___y_3019_ = v_a_3005_;
v___y_3020_ = v_a_3006_;
v___y_3021_ = v_a_3007_;
v___y_3022_ = v_a_3008_;
v___y_3023_ = v_a_3009_;
v___y_3024_ = v_a_3010_;
v___y_3025_ = v_a_3011_;
v___y_3026_ = v_a_3012_;
v___y_3027_ = v_a_3013_;
goto v___jp_3015_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_3076_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_a_3087_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3067_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3067_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
v___jp_3015_:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_3017_, v___y_3018_, v___y_3026_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3058_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3058_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3058_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_toRingState_3033_; lean_object* v_denote_3034_; uint8_t v___x_3035_; 
v_toRingState_3033_ = lean_ctor_get(v_a_3029_, 0);
lean_inc_ref(v_toRingState_3033_);
lean_dec(v_a_3029_);
v_denote_3034_ = lean_ctor_get(v_toRingState_3033_, 2);
lean_inc_ref(v_denote_3034_);
lean_dec_ref(v_toRingState_3033_);
v___x_3035_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_denote_3034_, v_one_3016_);
lean_dec_ref(v_denote_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_del_object(v___x_3031_);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = lean_box(0);
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc(v___y_3025_);
lean_inc_ref(v___y_3024_);
lean_inc(v___y_3023_);
lean_inc_ref(v___y_3022_);
lean_inc(v___y_3021_);
lean_inc_ref(v___y_3020_);
lean_inc(v___y_3019_);
lean_inc(v___y_3018_);
lean_inc_ref(v_one_3016_);
v___x_3038_ = lean_grind_internalize(v_one_3016_, v___x_3036_, v___x_3037_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v___x_3038_, 0);
lean_dec(v_unused_3046_);
v___x_3040_ = v___x_3038_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v___x_3038_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_one_3016_);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_one_3016_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_one_3016_);
v_a_3047_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3038_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3038_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v___x_3056_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_one_3016_);
v___x_3056_ = v___x_3031_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_one_3016_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v_one_3016_);
v_a_3059_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3028_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3028_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
return v_res_3107_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object* v_00_u03b2_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
uint8_t v___x_3111_; 
v___x_3111_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3109_, v_x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object* v_00_u03b2_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_){
_start:
{
uint8_t v_res_3115_; lean_object* v_r_3116_; 
v_res_3115_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(v_00_u03b2_3112_, v_x_3113_, v_x_3114_);
lean_dec_ref(v_x_3114_);
lean_dec_ref(v_x_3113_);
v_r_3116_ = lean_box(v_res_3115_);
return v_r_3116_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object* v_00_u03b2_3117_, lean_object* v_x_3118_, size_t v_x_3119_, lean_object* v_x_3120_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3118_, v_x_3119_, v_x_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_, lean_object* v_x_3125_){
_start:
{
size_t v_x_9875__boxed_3126_; uint8_t v_res_3127_; lean_object* v_r_3128_; 
v_x_9875__boxed_3126_ = lean_unbox_usize(v_x_3124_);
lean_dec(v_x_3124_);
v_res_3127_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(v_00_u03b2_3122_, v_x_3123_, v_x_9875__boxed_3126_, v_x_3125_);
lean_dec_ref(v_x_3125_);
lean_dec_ref(v_x_3123_);
v_r_3128_ = lean_box(v_res_3127_);
return v_r_3128_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3129_, lean_object* v_keys_3130_, lean_object* v_vals_3131_, lean_object* v_heq_3132_, lean_object* v_i_3133_, lean_object* v_k_3134_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3130_, v_i_3133_, v_k_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3136_, lean_object* v_keys_3137_, lean_object* v_vals_3138_, lean_object* v_heq_3139_, lean_object* v_i_3140_, lean_object* v_k_3141_){
_start:
{
uint8_t v_res_3142_; lean_object* v_r_3143_; 
v_res_3142_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(v_00_u03b2_3136_, v_keys_3137_, v_vals_3138_, v_heq_3139_, v_i_3140_, v_k_3141_);
lean_dec_ref(v_k_3141_);
lean_dec_ref(v_vals_3138_);
lean_dec_ref(v_keys_3137_);
v_r_3143_ = lean_box(v_res_3142_);
return v_r_3143_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Functions(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_MonadVar(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
}
#ifdef __cplusplus
}
#endif
