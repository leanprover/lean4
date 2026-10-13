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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_469_; lean_object* v_env_470_; uint8_t v___x_471_; lean_object* v_env_472_; lean_object* v___x_473_; lean_object* v_toCold_474_; lean_object* v_mctx_475_; lean_object* v_lctx_476_; lean_object* v_options_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_469_ = lean_st_ref_get(v___y_467_);
v_env_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_469_);
v___x_471_ = 0;
v_env_472_ = l_Lean_Environment_setRecordingDeps(v_env_470_, v___x_471_);
v___x_473_ = lean_st_ref_get(v___y_465_);
v_toCold_474_ = lean_ctor_get(v___y_466_, 0);
v_mctx_475_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_mctx_475_);
lean_dec(v___x_473_);
v_lctx_476_ = lean_ctor_get(v___y_464_, 2);
v_options_477_ = lean_ctor_get(v_toCold_474_, 2);
lean_inc_ref(v_options_477_);
lean_inc_ref(v_lctx_476_);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_env_472_);
lean_ctor_set(v___x_478_, 1, v_mctx_475_);
lean_ctor_set(v___x_478_, 2, v_lctx_476_);
lean_ctor_set(v___x_478_, 3, v_options_477_);
v___x_479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_msgData_463_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_ref_494_ = lean_ctor_get(v___y_491_, 2);
v___x_495_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_inc(v_ref_494_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_ref_494_);
lean_ctor_set(v___x_500_, 1, v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 1);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_521_, v_a_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_542_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_542_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_542_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_542_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_ringId_532_; lean_object* v_rings_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_ringId_532_ = lean_ctor_get(v_a_515_, 0);
v_rings_533_ = lean_ctor_get(v_a_528_, 1);
lean_inc_ref(v_rings_533_);
lean_dec(v_a_528_);
v___x_534_ = lean_array_get_size(v_rings_533_);
v___x_535_ = lean_nat_dec_lt(v_ringId_532_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_rings_533_);
lean_del_object(v___x_530_);
v___x_536_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_537_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_536_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_array_fget(v_rings_533_, v_ringId_532_);
lean_dec_ref(v_rings_533_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_538_);
v___x_540_ = v___x_530_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_527_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_527_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_565_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_579_, v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_594_, lean_object* v_f_595_, lean_object* v_s_596_){
_start:
{
lean_object* v_exp_597_; lean_object* v_rings_598_; lean_object* v_semirings_599_; lean_object* v_ncRings_600_; lean_object* v_ncSemirings_601_; lean_object* v_typeClassify_602_; lean_object* v_orders_603_; lean_object* v_typeOrderClassify_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_exp_597_ = lean_ctor_get(v_s_596_, 0);
v_rings_598_ = lean_ctor_get(v_s_596_, 1);
v_semirings_599_ = lean_ctor_get(v_s_596_, 2);
v_ncRings_600_ = lean_ctor_get(v_s_596_, 3);
v_ncSemirings_601_ = lean_ctor_get(v_s_596_, 4);
v_typeClassify_602_ = lean_ctor_get(v_s_596_, 5);
v_orders_603_ = lean_ctor_get(v_s_596_, 6);
v_typeOrderClassify_604_ = lean_ctor_get(v_s_596_, 7);
v___x_605_ = lean_array_get_size(v_rings_598_);
v___x_606_ = lean_nat_dec_lt(v_ringId_594_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_f_595_);
return v_s_596_;
}
else
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
lean_inc_ref(v_typeOrderClassify_604_);
lean_inc_ref(v_orders_603_);
lean_inc_ref(v_typeClassify_602_);
lean_inc_ref(v_ncSemirings_601_);
lean_inc_ref(v_ncRings_600_);
lean_inc_ref(v_semirings_599_);
lean_inc_ref(v_rings_598_);
lean_inc(v_exp_597_);
v_isSharedCheck_618_ = !lean_is_exclusive(v_s_596_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_619_ = lean_ctor_get(v_s_596_, 7);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_s_596_, 6);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_s_596_, 5);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_s_596_, 4);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_s_596_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_s_596_, 2);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_s_596_, 1);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_s_596_, 0);
lean_dec(v_unused_626_);
v___x_608_ = v_s_596_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_dec(v_s_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_v_610_; lean_object* v___x_611_; lean_object* v_xs_x27_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v_v_610_ = lean_array_fget(v_rings_598_, v_ringId_594_);
v___x_611_ = lean_box(0);
v_xs_x27_612_ = lean_array_fset(v_rings_598_, v_ringId_594_, v___x_611_);
v___x_613_ = lean_apply_1(v_f_595_, v_v_610_);
v___x_614_ = lean_array_fset(v_xs_x27_612_, v_ringId_594_, v___x_613_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_614_);
v___x_616_ = v___x_608_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_exp_597_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_semirings_599_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_ncRings_600_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_ncSemirings_601_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_typeClassify_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_orders_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_typeOrderClassify_604_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_627_, lean_object* v_f_628_, lean_object* v_s_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_627_, v_f_628_, v_s_629_);
lean_dec(v_ringId_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_ringId_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_ringId_635_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_ringId_635_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_636_, 0, v_ringId_635_);
lean_closure_set(v___f_636_, 1, v_f_631_);
v___x_637_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_638_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_637_, v___f_636_, v_a_633_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_644_, v_a_645_, v_a_651_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_671_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_674_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_691_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_691_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_ringId_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v_ringId_686_ = lean_ctor_get(v_a_677_, 0);
v___x_687_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_a_682_, v_ringId_686_);
lean_dec(v_a_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_681_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_681_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg___boxed(lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_700_, v_a_701_, v_a_702_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_705_, v_a_706_, v_a_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState(v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(lean_object* v_ringId_731_, lean_object* v_f_732_, lean_object* v_s_733_){
_start:
{
lean_object* v_rings_734_; lean_object* v_exprToRingId_735_; lean_object* v_semirings_736_; lean_object* v_exprToSemiringId_737_; lean_object* v_ncRings_738_; lean_object* v_exprToNCRingId_739_; lean_object* v_ncSemirings_740_; lean_object* v_exprToNCSemiringId_741_; lean_object* v_steps_742_; uint8_t v_reportedMaxDegreeIssue_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_764_; 
v_rings_734_ = lean_ctor_get(v_s_733_, 0);
v_exprToRingId_735_ = lean_ctor_get(v_s_733_, 1);
v_semirings_736_ = lean_ctor_get(v_s_733_, 2);
v_exprToSemiringId_737_ = lean_ctor_get(v_s_733_, 3);
v_ncRings_738_ = lean_ctor_get(v_s_733_, 4);
v_exprToNCRingId_739_ = lean_ctor_get(v_s_733_, 5);
v_ncSemirings_740_ = lean_ctor_get(v_s_733_, 6);
v_exprToNCSemiringId_741_ = lean_ctor_get(v_s_733_, 7);
v_steps_742_ = lean_ctor_get(v_s_733_, 8);
v_reportedMaxDegreeIssue_743_ = lean_ctor_get_uint8(v_s_733_, sizeof(void*)*9);
v_isSharedCheck_764_ = !lean_is_exclusive(v_s_733_);
if (v_isSharedCheck_764_ == 0)
{
v___x_745_ = v_s_733_;
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_steps_742_);
lean_inc(v_exprToNCSemiringId_741_);
lean_inc(v_ncSemirings_740_);
lean_inc(v_exprToNCRingId_739_);
lean_inc(v_ncRings_738_);
lean_inc(v_exprToSemiringId_737_);
lean_inc(v_semirings_736_);
lean_inc(v_exprToRingId_735_);
lean_inc(v_rings_734_);
lean_dec(v_s_733_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_764_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_add(v_ringId_731_, v___x_747_);
v___x_749_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_750_ = l_Array_rightpad___redArg(v___x_748_, v___x_749_, v_rings_734_);
lean_dec(v___x_748_);
v___x_751_ = lean_array_get_size(v___x_750_);
v___x_752_ = lean_nat_dec_lt(v_ringId_731_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_754_; 
lean_dec_ref(v_f_732_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_750_);
v___x_754_ = v___x_745_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_exprToRingId_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_semirings_736_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_exprToSemiringId_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_ncRings_738_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v_exprToNCRingId_739_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_ncSemirings_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v_exprToNCSemiringId_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_steps_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_755_, sizeof(void*)*9, v_reportedMaxDegreeIssue_743_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v_v_756_; lean_object* v___x_757_; lean_object* v_xs_x27_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v_v_756_ = lean_array_fget(v___x_750_, v_ringId_731_);
v___x_757_ = lean_box(0);
v_xs_x27_758_ = lean_array_fset(v___x_750_, v_ringId_731_, v___x_757_);
v___x_759_ = lean_apply_1(v_f_732_, v_v_756_);
v___x_760_ = lean_array_fset(v_xs_x27_758_, v_ringId_731_, v___x_759_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_760_);
v___x_762_ = v___x_745_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_exprToRingId_735_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_semirings_736_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_exprToSemiringId_737_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_ncRings_738_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_exprToNCRingId_739_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_ncSemirings_740_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v_exprToNCSemiringId_741_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_steps_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*9, v_reportedMaxDegreeIssue_743_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed(lean_object* v_ringId_765_, lean_object* v_f_766_, lean_object* v_s_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0(v_ringId_765_, v_f_766_, v_s_767_);
lean_dec(v_ringId_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object* v_f_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_ringId_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_ringId_773_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_ringId_773_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_774_, 0, v_ringId_773_);
lean_closure_set(v___f_774_, 1, v_f_769_);
v___x_775_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_776_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_775_, v___f_774_, v_a_771_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg___boxed(lean_object* v_f_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(lean_object* v_f_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v_f_782_, v_a_783_, v_a_784_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object* v_f_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState(v_f_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__0));
v___x_812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed), 12, 0);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM___closed__1);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(lean_object* v___x_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_817_, v___y_818_, v___y_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_846_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_846_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_846_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_846_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_toRingState_834_; lean_object* v_vars_835_; lean_object* v_size_836_; uint8_t v___x_837_; 
v_toRingState_834_ = lean_ctor_get(v_a_830_, 0);
lean_inc_ref(v_toRingState_834_);
lean_dec(v_a_830_);
v_vars_835_ = lean_ctor_get(v_toRingState_834_, 0);
lean_inc_ref(v_vars_835_);
lean_dec_ref(v_toRingState_834_);
v_size_836_ = lean_ctor_get(v_vars_835_, 2);
v___x_837_ = lean_nat_dec_lt(v_x_816_, v_size_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec_ref(v_vars_835_);
v___x_838_ = l_outOfBounds___redArg(v___x_815_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_838_);
v___x_840_ = v___x_832_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = l_Lean_PersistentArray_get_x21___redArg(v___x_815_, v_vars_835_, v_x_816_);
lean_dec_ref(v_vars_835_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_842_);
v___x_844_ = v___x_832_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
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
v_a_847_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_829_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_829_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed(lean_object* v___x_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0(v___x_855_, v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v_x_856_);
lean_dec_ref(v___x_855_);
return v_res_869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0(void){
_start:
{
lean_object* v___x_870_; lean_object* v___f_871_; 
v___x_870_ = l_Lean_instInhabitedExpr;
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___lam__0___boxed), 14, 1);
lean_closure_set(v___f_871_, 0, v___x_870_);
return v___f_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM(void){
_start:
{
lean_object* v___f_872_; 
v___f_872_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadGetVarRingM___closed__0);
return v___f_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_ringId_886_; lean_object* v_gen_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_ringId_886_ = lean_ctor_get(v_a_874_, 0);
v_gen_887_ = lean_ctor_get(v_a_874_, 1);
v___x_888_ = 1;
lean_inc(v_gen_887_);
lean_inc(v_ringId_886_);
v___x_889_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_889_, 0, v_ringId_886_);
lean_ctor_set(v___x_889_, 1, v_gen_887_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*2, v___x_888_);
lean_inc(v_a_884_);
lean_inc_ref(v_a_883_);
lean_inc(v_a_882_);
lean_inc_ref(v_a_881_);
lean_inc(v_a_880_);
lean_inc_ref(v_a_879_);
lean_inc(v_a_878_);
lean_inc_ref(v_a_877_);
lean_inc(v_a_876_);
lean_inc(v_a_875_);
v___x_890_ = lean_apply_12(v_x_873_, v___x_889_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, lean_box(0));
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_905_, lean_object* v_x_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_ringId_919_; lean_object* v_gen_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_ringId_919_ = lean_ctor_get(v_a_907_, 0);
v_gen_920_ = lean_ctor_get(v_a_907_, 1);
v___x_921_ = 1;
lean_inc(v_gen_920_);
lean_inc(v_ringId_919_);
v___x_922_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_922_, 0, v_ringId_919_);
lean_ctor_set(v___x_922_, 1, v_gen_920_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*2, v___x_921_);
lean_inc(v_a_917_);
lean_inc_ref(v_a_916_);
lean_inc(v_a_915_);
lean_inc_ref(v_a_914_);
lean_inc(v_a_913_);
lean_inc_ref(v_a_912_);
lean_inc(v_a_911_);
lean_inc_ref(v_a_910_);
lean_inc(v_a_909_);
lean_inc(v_a_908_);
v___x_923_ = lean_apply_12(v_x_906_, v___x_922_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, lean_box(0));
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_924_, lean_object* v_x_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_924_, v_x_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
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
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_939_){
_start:
{
uint8_t v_checkCoeffDvd_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_checkCoeffDvd_941_ = lean_ctor_get_uint8(v_a_939_, sizeof(void*)*2);
v___x_942_ = lean_box(v_checkCoeffDvd_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_944_);
lean_dec_ref(v_a_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_947_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_973_, lean_object* v_vals_974_, lean_object* v_i_975_, lean_object* v_k_976_){
_start:
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_array_get_size(v_keys_973_);
v___x_978_ = lean_nat_dec_lt(v_i_975_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec(v_i_975_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
else
{
lean_object* v_k_x27_980_; size_t v___x_981_; size_t v___x_982_; uint8_t v___x_983_; 
v_k_x27_980_ = lean_array_fget_borrowed(v_keys_973_, v_i_975_);
v___x_981_ = lean_ptr_addr(v_k_976_);
v___x_982_ = lean_ptr_addr(v_k_x27_980_);
v___x_983_ = lean_usize_dec_eq(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_add(v_i_975_, v___x_984_);
lean_dec(v_i_975_);
v_i_975_ = v___x_985_;
goto _start;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_array_fget_borrowed(v_vals_974_, v_i_975_);
lean_dec(v_i_975_);
lean_inc(v___x_987_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_i_991_, lean_object* v_k_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_989_, v_vals_990_, v_i_991_, v_k_992_);
lean_dec_ref(v_k_992_);
lean_dec_ref(v_vals_990_);
lean_dec_ref(v_keys_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_994_, size_t v_x_995_, lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
lean_object* v_es_997_; lean_object* v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v_j_1001_; lean_object* v___x_1002_; 
v_es_997_ = lean_ctor_get(v_x_994_, 0);
v___x_998_ = lean_box(2);
v___x_999_ = ((size_t)31ULL);
v___x_1000_ = lean_usize_land(v_x_995_, v___x_999_);
v_j_1001_ = lean_usize_to_nat(v___x_1000_);
v___x_1002_ = lean_array_get_borrowed(v___x_998_, v_es_997_, v_j_1001_);
lean_dec(v_j_1001_);
switch(lean_obj_tag(v___x_1002_))
{
case 0:
{
lean_object* v_key_1003_; lean_object* v_val_1004_; size_t v___x_1005_; size_t v___x_1006_; uint8_t v___x_1007_; 
v_key_1003_ = lean_ctor_get(v___x_1002_, 0);
v_val_1004_ = lean_ctor_get(v___x_1002_, 1);
v___x_1005_ = lean_ptr_addr(v_x_996_);
v___x_1006_ = lean_ptr_addr(v_key_1003_);
v___x_1007_ = lean_usize_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; 
lean_inc(v_val_1004_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_val_1004_);
return v___x_1009_;
}
}
case 1:
{
lean_object* v_node_1010_; size_t v___x_1011_; size_t v___x_1012_; 
v_node_1010_ = lean_ctor_get(v___x_1002_, 0);
v___x_1011_ = ((size_t)5ULL);
v___x_1012_ = lean_usize_shift_right(v_x_995_, v___x_1011_);
v_x_994_ = v_node_1010_;
v_x_995_ = v___x_1012_;
goto _start;
}
default: 
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
}
}
else
{
lean_object* v_ks_1015_; lean_object* v_vs_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_ks_1015_ = lean_ctor_get(v_x_994_, 0);
v_vs_1016_ = lean_ctor_get(v_x_994_, 1);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1015_, v_vs_1016_, v___x_1017_, v_x_996_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
size_t v_x_905__boxed_1022_; lean_object* v_res_1023_; 
v_x_905__boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_res_1023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1019_, v_x_905__boxed_1022_, v_x_1021_);
lean_dec_ref(v_x_1021_);
lean_dec_ref(v_x_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
size_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; uint64_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1026_ = lean_ptr_addr(v_x_1025_);
v___x_1027_ = ((size_t)3ULL);
v___x_1028_ = lean_usize_shift_right(v___x_1026_, v___x_1027_);
v___x_1029_ = lean_usize_to_uint64(v___x_1028_);
v___x_1030_ = lean_uint64_to_usize(v___x_1029_);
v___x_1031_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1024_, v___x_1030_, v_x_1025_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1032_, v_x_1033_);
lean_dec_ref(v_x_1033_);
lean_dec_ref(v_x_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1049_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_exprToRingId_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v_exprToRingId_1044_ = lean_ctor_get(v_a_1040_, 1);
lean_inc_ref(v_exprToRingId_1044_);
lean_dec(v_a_1040_);
v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_1044_, v_e_1035_);
lean_dec_ref(v_exprToRingId_1044_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1039_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1039_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_e_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_1063_, v_a_1064_, v_a_1072_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_e_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_1093_, v_x_1094_, v_x_1095_);
lean_dec_ref(v_x_1095_);
lean_dec_ref(v_x_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, size_t v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_1098_, v_x_1099_, v_x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
size_t v_x_1026__boxed_1106_; lean_object* v_res_1107_; 
v_x_1026__boxed_1106_ = lean_unbox_usize(v_x_1104_);
lean_dec(v_x_1104_);
v_res_1107_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_1102_, v_x_1103_, v_x_1026__boxed_1106_, v_x_1105_);
lean_dec_ref(v_x_1105_);
lean_dec_ref(v_x_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1108_, lean_object* v_keys_1109_, lean_object* v_vals_1110_, lean_object* v_heq_1111_, lean_object* v_i_1112_, lean_object* v_k_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1109_, v_vals_1110_, v_i_1112_, v_k_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1115_, lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_heq_1118_, lean_object* v_i_1119_, lean_object* v_k_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1115_, v_keys_1116_, v_vals_1117_, v_heq_1118_, v_i_1119_, v_k_1120_);
lean_dec_ref(v_k_1120_);
lean_dec_ref(v_vals_1117_);
lean_dec_ref(v_keys_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_1122_, lean_object* v_____do__lift_1123_){
_start:
{
lean_object* v_charInst_x3f_1127_; 
v_charInst_x3f_1127_ = lean_ctor_get(v_____do__lift_1123_, 5);
lean_inc(v_charInst_x3f_1127_);
lean_dec_ref(v_____do__lift_1123_);
if (lean_obj_tag(v_charInst_x3f_1127_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1139_; 
v_val_1128_ = lean_ctor_get(v_charInst_x3f_1127_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_charInst_x3f_1127_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1130_ = v_charInst_x3f_1127_;
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v_charInst_x3f_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_snd_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_snd_1132_ = lean_ctor_get(v_val_1128_, 1);
lean_inc(v_snd_1132_);
lean_dec(v_val_1128_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_nat_dec_eq(v_snd_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1136_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_snd_1132_);
v___x_1136_ = v___x_1130_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_snd_1132_);
v___x_1136_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_apply_2(v_toPure_1122_, lean_box(0), v___x_1136_);
return v___x_1137_;
}
}
else
{
lean_dec(v_snd_1132_);
lean_del_object(v___x_1130_);
goto v___jp_1124_;
}
}
}
else
{
lean_dec(v_charInst_x3f_1127_);
goto v___jp_1124_;
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_apply_2(v_toPure_1122_, lean_box(0), v___x_1125_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v_toApplicative_1142_; lean_object* v_toBind_1143_; lean_object* v_getRing_1144_; lean_object* v_toPure_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v_toApplicative_1142_ = lean_ctor_get(v_inst_1140_, 0);
lean_inc_ref(v_toApplicative_1142_);
v_toBind_1143_ = lean_ctor_get(v_inst_1140_, 1);
lean_inc(v_toBind_1143_);
lean_dec_ref(v_inst_1140_);
v_getRing_1144_ = lean_ctor_get(v_inst_1141_, 0);
lean_inc(v_getRing_1144_);
lean_dec_ref(v_inst_1141_);
v_toPure_1145_ = lean_ctor_get(v_toApplicative_1142_, 1);
lean_inc(v_toPure_1145_);
lean_dec_ref(v_toApplicative_1142_);
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1146_, 0, v_toPure_1145_);
v___x_1147_ = lean_apply_4(v_toBind_1143_, lean_box(0), lean_box(0), v_getRing_1144_, v___f_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_1149_, v_inst_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_1152_, lean_object* v_____do__lift_1153_){
_start:
{
lean_object* v_charInst_x3f_1157_; 
v_charInst_x3f_1157_ = lean_ctor_get(v_____do__lift_1153_, 5);
lean_inc(v_charInst_x3f_1157_);
lean_dec_ref(v_____do__lift_1153_);
if (lean_obj_tag(v_charInst_x3f_1157_) == 1)
{
lean_object* v_val_1158_; lean_object* v_snd_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_val_1158_ = lean_ctor_get(v_charInst_x3f_1157_, 0);
v_snd_1159_ = lean_ctor_get(v_val_1158_, 1);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_nat_dec_eq(v_snd_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_apply_2(v_toPure_1152_, lean_box(0), v_charInst_x3f_1157_);
return v___x_1162_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_1157_, 1);
goto v___jp_1154_;
}
}
else
{
lean_dec(v_charInst_x3f_1157_);
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_apply_2(v_toPure_1152_, lean_box(0), v___x_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_1163_, lean_object* v_inst_1164_){
_start:
{
lean_object* v_toApplicative_1165_; lean_object* v_toBind_1166_; lean_object* v_getRing_1167_; lean_object* v_toPure_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_toApplicative_1165_ = lean_ctor_get(v_inst_1163_, 0);
lean_inc_ref(v_toApplicative_1165_);
v_toBind_1166_ = lean_ctor_get(v_inst_1163_, 1);
lean_inc(v_toBind_1166_);
lean_dec_ref(v_inst_1163_);
v_getRing_1167_ = lean_ctor_get(v_inst_1164_, 0);
lean_inc(v_getRing_1167_);
lean_dec_ref(v_inst_1164_);
v_toPure_1168_ = lean_ctor_get(v_toApplicative_1165_, 1);
lean_inc(v_toPure_1168_);
lean_dec_ref(v_toApplicative_1165_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1169_, 0, v_toPure_1168_);
v___x_1170_ = lean_apply_4(v_toBind_1166_, lean_box(0), lean_box(0), v_getRing_1167_, v___f_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_1172_, v_inst_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_noZeroDivInst_x3f_1192_; lean_object* v___x_1194_; 
v_noZeroDivInst_x3f_1192_ = lean_ctor_get(v_a_1188_, 6);
lean_inc(v_noZeroDivInst_x3f_1192_);
lean_dec(v_a_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v_noZeroDivInst_x3f_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_noZeroDivInst_x3f_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1187_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1187_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1246_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1246_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1246_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_noZeroDivInst_x3f_1235_; 
v_noZeroDivInst_x3f_1235_ = lean_ctor_get(v_a_1231_, 6);
lean_inc(v_noZeroDivInst_x3f_1235_);
lean_dec(v_a_1231_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1235_) == 0)
{
uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = 0;
v___x_1237_ = lean_box(v___x_1236_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1237_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1235_, 1);
v___x_1241_ = 1;
v___x_1242_ = lean_box(v___x_1241_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1242_);
v___x_1244_ = v___x_1233_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1230_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1230_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1297_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1297_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1297_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_toRing_1285_; lean_object* v_charInst_x3f_1286_; 
v_toRing_1285_ = lean_ctor_get(v_a_1281_, 0);
lean_inc_ref(v_toRing_1285_);
lean_dec(v_a_1281_);
v_charInst_x3f_1286_ = lean_ctor_get(v_toRing_1285_, 5);
lean_inc(v_charInst_x3f_1286_);
lean_dec_ref(v_toRing_1285_);
if (lean_obj_tag(v_charInst_x3f_1286_) == 0)
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = 0;
v___x_1288_ = lean_box(v___x_1287_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1288_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
lean_dec_ref_known(v_charInst_x3f_1286_, 1);
v___x_1292_ = 1;
v___x_1293_ = lean_box(v___x_1292_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1293_);
v___x_1295_ = v___x_1283_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1280_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1280_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1347_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_toRing_1339_; lean_object* v_charInst_x3f_1340_; 
v_toRing_1339_ = lean_ctor_get(v_a_1335_, 0);
lean_inc_ref(v_toRing_1339_);
lean_dec(v_a_1335_);
v_charInst_x3f_1340_ = lean_ctor_get(v_toRing_1339_, 5);
lean_inc(v_charInst_x3f_1340_);
lean_dec_ref(v_toRing_1339_);
if (lean_obj_tag(v_charInst_x3f_1340_) == 1)
{
lean_object* v_val_1341_; lean_object* v___x_1343_; 
v_val_1341_ = lean_ctor_get(v_charInst_x3f_1340_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v_charInst_x3f_1340_, 1);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_val_1341_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_val_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_charInst_x3f_1340_);
lean_del_object(v___x_1337_);
v___x_1345_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1346_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1345_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1334_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1334_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1397_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1397_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1397_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_fieldInst_x3f_1386_; 
v_fieldInst_x3f_1386_ = lean_ctor_get(v_a_1382_, 7);
lean_inc(v_fieldInst_x3f_1386_);
lean_dec(v_a_1382_);
if (lean_obj_tag(v_fieldInst_x3f_1386_) == 0)
{
uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1387_ = 0;
v___x_1388_ = lean_box(v___x_1387_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_dec_ref_known(v_fieldInst_x3f_1386_, 1);
v___x_1392_ = 1;
v___x_1393_ = lean_box(v___x_1392_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1393_);
v___x_1395_ = v___x_1384_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1381_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1381_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1419_, v_a_1420_, v_a_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1439_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1439_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1439_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_queue_1428_; 
v_queue_1428_ = lean_ctor_get(v_a_1424_, 4);
lean_inc(v_queue_1428_);
lean_dec(v_a_1424_);
if (lean_obj_tag(v_queue_1428_) == 0)
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec_ref_known(v_queue_1428_, 5);
v___x_1429_ = 0;
v___x_1430_ = lean_box(v___x_1429_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1430_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = 1;
v___x_1435_ = lean_box(v___x_1434_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1435_);
v___x_1437_ = v___x_1426_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1423_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1423_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg___boxed(lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___redArg(v_a_1453_, v_a_1454_, v_a_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1479_, lean_object* v_t_1480_){
_start:
{
if (lean_obj_tag(v_t_1480_) == 0)
{
lean_object* v_k_1481_; lean_object* v_v_1482_; lean_object* v_l_1483_; lean_object* v_r_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_2138_; 
v_k_1481_ = lean_ctor_get(v_t_1480_, 1);
v_v_1482_ = lean_ctor_get(v_t_1480_, 2);
v_l_1483_ = lean_ctor_get(v_t_1480_, 3);
v_r_1484_ = lean_ctor_get(v_t_1480_, 4);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_t_1480_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v_t_1480_, 0);
lean_dec(v_unused_2139_);
v___x_1486_ = v_t_1480_;
v_isShared_1487_ = v_isSharedCheck_2138_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_r_1484_);
lean_inc(v_l_1483_);
lean_inc(v_v_1482_);
lean_inc(v_k_1481_);
lean_dec(v_t_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_2138_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1479_, v_k_1481_);
switch(v___x_1488_)
{
case 0:
{
lean_object* v_impl_1489_; lean_object* v___x_1490_; 
v_impl_1489_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1479_, v_l_1483_);
v___x_1490_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1489_) == 0)
{
if (lean_obj_tag(v_r_1484_) == 0)
{
lean_object* v_size_1491_; lean_object* v_size_1492_; lean_object* v_k_1493_; lean_object* v_v_1494_; lean_object* v_l_1495_; lean_object* v_r_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_size_1491_ = lean_ctor_get(v_impl_1489_, 0);
v_size_1492_ = lean_ctor_get(v_r_1484_, 0);
v_k_1493_ = lean_ctor_get(v_r_1484_, 1);
v_v_1494_ = lean_ctor_get(v_r_1484_, 2);
v_l_1495_ = lean_ctor_get(v_r_1484_, 3);
lean_inc(v_l_1495_);
v_r_1496_ = lean_ctor_get(v_r_1484_, 4);
v___x_1497_ = lean_unsigned_to_nat(3u);
v___x_1498_ = lean_nat_mul(v___x_1497_, v_size_1491_);
v___x_1499_ = lean_nat_dec_lt(v___x_1498_, v_size_1492_);
lean_dec(v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec(v_l_1495_);
v___x_1500_ = lean_nat_add(v___x_1490_, v_size_1491_);
v___x_1501_ = lean_nat_add(v___x_1500_, v_size_1492_);
lean_dec(v___x_1500_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 3, v_impl_1489_);
lean_ctor_set(v___x_1486_, 0, v___x_1501_);
v___x_1503_ = v___x_1486_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_impl_1489_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_r_1484_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
else
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1568_; 
lean_inc(v_r_1496_);
lean_inc(v_v_1494_);
lean_inc(v_k_1493_);
lean_inc(v_size_1492_);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; lean_object* v_unused_1570_; lean_object* v_unused_1571_; lean_object* v_unused_1572_; lean_object* v_unused_1573_; 
v_unused_1569_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_r_1484_, 2);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_r_1484_, 1);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1573_);
v___x_1506_ = v_r_1484_;
v_isShared_1507_ = v_isSharedCheck_1568_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_r_1484_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1568_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_size_1508_; lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v_l_1511_; lean_object* v_r_1512_; lean_object* v_size_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v_size_1508_ = lean_ctor_get(v_l_1495_, 0);
v_k_1509_ = lean_ctor_get(v_l_1495_, 1);
v_v_1510_ = lean_ctor_get(v_l_1495_, 2);
v_l_1511_ = lean_ctor_get(v_l_1495_, 3);
v_r_1512_ = lean_ctor_get(v_l_1495_, 4);
v_size_1513_ = lean_ctor_get(v_r_1496_, 0);
v___x_1514_ = lean_unsigned_to_nat(2u);
v___x_1515_ = lean_nat_mul(v___x_1514_, v_size_1513_);
v___x_1516_ = lean_nat_dec_lt(v_size_1508_, v___x_1515_);
lean_dec(v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1544_; 
lean_inc(v_r_1512_);
lean_inc(v_l_1511_);
lean_inc(v_v_1510_);
lean_inc(v_k_1509_);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_l_1495_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1545_ = lean_ctor_get(v_l_1495_, 4);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_l_1495_, 3);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_l_1495_, 2);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_l_1495_, 1);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_l_1495_, 0);
lean_dec(v_unused_1549_);
v___x_1518_ = v_l_1495_;
v_isShared_1519_ = v_isSharedCheck_1544_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_l_1495_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1544_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1534_; 
v___x_1520_ = lean_nat_add(v___x_1490_, v_size_1491_);
v___x_1521_ = lean_nat_add(v___x_1520_, v_size_1492_);
lean_dec(v_size_1492_);
if (lean_obj_tag(v_l_1511_) == 0)
{
lean_object* v_size_1542_; 
v_size_1542_ = lean_ctor_get(v_l_1511_, 0);
lean_inc(v_size_1542_);
v___y_1534_ = v_size_1542_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_unsigned_to_nat(0u);
v___y_1534_ = v___x_1543_;
goto v___jp_1533_;
}
v___jp_1522_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_nat_add(v___y_1523_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec(v___y_1523_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 4, v_r_1496_);
lean_ctor_set(v___x_1518_, 3, v_r_1512_);
lean_ctor_set(v___x_1518_, 2, v_v_1494_);
lean_ctor_set(v___x_1518_, 1, v_k_1493_);
lean_ctor_set(v___x_1518_, 0, v___x_1526_);
v___x_1528_ = v___x_1518_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1493_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1494_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_r_1512_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_r_1496_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v___x_1528_);
lean_ctor_set(v___x_1506_, 3, v___y_1524_);
lean_ctor_set(v___x_1506_, 2, v_v_1510_);
lean_ctor_set(v___x_1506_, 1, v_k_1509_);
lean_ctor_set(v___x_1506_, 0, v___x_1521_);
v___x_1530_ = v___x_1506_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___y_1524_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_nat_add(v___x_1520_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec(v___x_1520_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_l_1511_);
lean_ctor_set(v___x_1486_, 3, v_impl_1489_);
lean_ctor_set(v___x_1486_, 0, v___x_1535_);
v___x_1537_ = v___x_1486_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_impl_1489_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_l_1511_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_nat_add(v___x_1490_, v_size_1513_);
if (lean_obj_tag(v_r_1512_) == 0)
{
lean_object* v_size_1539_; 
v_size_1539_ = lean_ctor_get(v_r_1512_, 0);
lean_inc(v_size_1539_);
v___y_1523_ = v___x_1538_;
v___y_1524_ = v___x_1537_;
v___y_1525_ = v_size_1539_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___y_1523_ = v___x_1538_;
v___y_1524_ = v___x_1537_;
v___y_1525_ = v___x_1540_;
goto v___jp_1522_;
}
}
}
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_del_object(v___x_1486_);
v___x_1550_ = lean_nat_add(v___x_1490_, v_size_1491_);
v___x_1551_ = lean_nat_add(v___x_1550_, v_size_1492_);
lean_dec(v_size_1492_);
v___x_1552_ = lean_nat_add(v___x_1550_, v_size_1508_);
lean_dec(v___x_1550_);
lean_inc_ref(v_impl_1489_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v_l_1495_);
lean_ctor_set(v___x_1506_, 3, v_impl_1489_);
lean_ctor_set(v___x_1506_, 2, v_v_1482_);
lean_ctor_set(v___x_1506_, 1, v_k_1481_);
lean_ctor_set(v___x_1506_, 0, v___x_1552_);
v___x_1554_ = v___x_1506_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_impl_1489_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_l_1495_);
v___x_1554_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_isSharedCheck_1561_ = !lean_is_exclusive(v_impl_1489_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; lean_object* v_unused_1566_; 
v_unused_1562_ = lean_ctor_get(v_impl_1489_, 4);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_impl_1489_, 3);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_impl_1489_, 2);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_impl_1489_, 1);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_impl_1489_, 0);
lean_dec(v_unused_1566_);
v___x_1556_ = v_impl_1489_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_impl_1489_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v_r_1496_);
lean_ctor_set(v___x_1556_, 3, v___x_1554_);
lean_ctor_set(v___x_1556_, 2, v_v_1494_);
lean_ctor_set(v___x_1556_, 1, v_k_1493_);
lean_ctor_set(v___x_1556_, 0, v___x_1551_);
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_k_1493_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_v_1494_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_r_1496_);
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
}
}
else
{
lean_object* v_size_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v_size_1574_ = lean_ctor_get(v_impl_1489_, 0);
v___x_1575_ = lean_nat_add(v___x_1490_, v_size_1574_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 3, v_impl_1489_);
lean_ctor_set(v___x_1486_, 0, v___x_1575_);
v___x_1577_ = v___x_1486_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_impl_1489_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_r_1484_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
if (lean_obj_tag(v_r_1484_) == 0)
{
lean_object* v_l_1579_; 
v_l_1579_ = lean_ctor_get(v_r_1484_, 3);
lean_inc(v_l_1579_);
if (lean_obj_tag(v_l_1579_) == 0)
{
lean_object* v_r_1580_; 
v_r_1580_ = lean_ctor_get(v_r_1484_, 4);
lean_inc(v_r_1580_);
if (lean_obj_tag(v_r_1580_) == 0)
{
lean_object* v_size_1581_; lean_object* v_k_1582_; lean_object* v_v_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1596_; 
v_size_1581_ = lean_ctor_get(v_r_1484_, 0);
v_k_1582_ = lean_ctor_get(v_r_1484_, 1);
v_v_1583_ = lean_ctor_get(v_r_1484_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; 
v_unused_1597_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1598_);
v___x_1585_ = v_r_1484_;
v_isShared_1586_ = v_isSharedCheck_1596_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_v_1583_);
lean_inc(v_k_1582_);
lean_inc(v_size_1581_);
lean_dec(v_r_1484_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1596_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_size_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_size_1587_ = lean_ctor_get(v_l_1579_, 0);
v___x_1588_ = lean_nat_add(v___x_1490_, v_size_1581_);
lean_dec(v_size_1581_);
v___x_1589_ = lean_nat_add(v___x_1490_, v_size_1587_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 4, v_l_1579_);
lean_ctor_set(v___x_1585_, 3, v_impl_1489_);
lean_ctor_set(v___x_1585_, 2, v_v_1482_);
lean_ctor_set(v___x_1585_, 1, v_k_1481_);
lean_ctor_set(v___x_1585_, 0, v___x_1589_);
v___x_1591_ = v___x_1585_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_impl_1489_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_l_1579_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_r_1580_);
lean_ctor_set(v___x_1486_, 3, v___x_1591_);
lean_ctor_set(v___x_1486_, 2, v_v_1583_);
lean_ctor_set(v___x_1486_, 1, v_k_1582_);
lean_ctor_set(v___x_1486_, 0, v___x_1588_);
v___x_1593_ = v___x_1486_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1582_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1583_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_r_1580_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_k_1599_; lean_object* v_v_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1623_; 
v_k_1599_ = lean_ctor_get(v_r_1484_, 1);
v_v_1600_ = lean_ctor_get(v_r_1484_, 2);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1624_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1626_);
v___x_1602_ = v_r_1484_;
v_isShared_1603_ = v_isSharedCheck_1623_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_v_1600_);
lean_inc(v_k_1599_);
lean_dec(v_r_1484_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1623_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1619_; 
v_k_1604_ = lean_ctor_get(v_l_1579_, 1);
v_v_1605_ = lean_ctor_get(v_l_1579_, 2);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_l_1579_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1620_ = lean_ctor_get(v_l_1579_, 4);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_l_1579_, 3);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_l_1579_, 0);
lean_dec(v_unused_1622_);
v___x_1607_ = v_l_1579_;
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_v_1605_);
lean_inc(v_k_1604_);
lean_dec(v_l_1579_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_unsigned_to_nat(3u);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 4, v_r_1580_);
lean_ctor_set(v___x_1607_, 3, v_r_1580_);
lean_ctor_set(v___x_1607_, 2, v_v_1482_);
lean_ctor_set(v___x_1607_, 1, v_k_1481_);
lean_ctor_set(v___x_1607_, 0, v___x_1490_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_r_1580_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_r_1580_);
v___x_1611_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 3, v_r_1580_);
lean_ctor_set(v___x_1602_, 0, v___x_1490_);
v___x_1613_ = v___x_1602_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1599_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1600_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_r_1580_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_r_1580_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1613_);
lean_ctor_set(v___x_1486_, 3, v___x_1611_);
lean_ctor_set(v___x_1486_, 2, v_v_1605_);
lean_ctor_set(v___x_1486_, 1, v_k_1604_);
lean_ctor_set(v___x_1486_, 0, v___x_1609_);
v___x_1615_ = v___x_1486_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_k_1604_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_v_1605_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1627_; 
v_r_1627_ = lean_ctor_get(v_r_1484_, 4);
lean_inc(v_r_1627_);
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_k_1628_; lean_object* v_v_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1640_; 
v_k_1628_ = lean_ctor_get(v_r_1484_, 1);
v_v_1629_ = lean_ctor_get(v_r_1484_, 2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; 
v_unused_1641_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1643_);
v___x_1631_ = v_r_1484_;
v_isShared_1632_ = v_isSharedCheck_1640_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_v_1629_);
lean_inc(v_k_1628_);
lean_dec(v_r_1484_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1640_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_unsigned_to_nat(3u);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v_l_1579_);
lean_ctor_set(v___x_1631_, 2, v_v_1482_);
lean_ctor_set(v___x_1631_, 1, v_k_1481_);
lean_ctor_set(v___x_1631_, 0, v___x_1490_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1579_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_l_1579_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_r_1627_);
lean_ctor_set(v___x_1486_, 3, v___x_1635_);
lean_ctor_set(v___x_1486_, 2, v_v_1629_);
lean_ctor_set(v___x_1486_, 1, v_k_1628_);
lean_ctor_set(v___x_1486_, 0, v___x_1633_);
v___x_1637_ = v___x_1486_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_r_1627_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_size_1644_; lean_object* v_k_1645_; lean_object* v_v_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1657_; 
v_size_1644_ = lean_ctor_get(v_r_1484_, 0);
v_k_1645_ = lean_ctor_get(v_r_1484_, 1);
v_v_1646_ = lean_ctor_get(v_r_1484_, 2);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; lean_object* v_unused_1659_; 
v_unused_1658_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1658_);
v_unused_1659_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1659_);
v___x_1648_ = v_r_1484_;
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_v_1646_);
lean_inc(v_k_1645_);
lean_inc(v_size_1644_);
lean_dec(v_r_1484_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1657_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 3, v_r_1627_);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_size_1644_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_k_1645_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_v_1646_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_r_1627_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_r_1627_);
v___x_1651_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(2u);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1651_);
lean_ctor_set(v___x_1486_, 3, v_r_1627_);
lean_ctor_set(v___x_1486_, 0, v___x_1652_);
v___x_1654_ = v___x_1486_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_r_1627_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v___x_1651_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
else
{
lean_object* v___x_1661_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 3, v_r_1484_);
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1661_ = v___x_1486_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_r_1484_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_r_1484_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1486_);
lean_dec(v_v_1482_);
lean_dec(v_k_1481_);
if (lean_obj_tag(v_l_1483_) == 0)
{
if (lean_obj_tag(v_r_1484_) == 0)
{
lean_object* v_size_1663_; lean_object* v_k_1664_; lean_object* v_v_1665_; lean_object* v_l_1666_; lean_object* v_r_1667_; lean_object* v_size_1668_; lean_object* v_k_1669_; lean_object* v_v_1670_; lean_object* v_l_1671_; lean_object* v_r_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_size_1663_ = lean_ctor_get(v_l_1483_, 0);
v_k_1664_ = lean_ctor_get(v_l_1483_, 1);
v_v_1665_ = lean_ctor_get(v_l_1483_, 2);
v_l_1666_ = lean_ctor_get(v_l_1483_, 3);
v_r_1667_ = lean_ctor_get(v_l_1483_, 4);
lean_inc(v_r_1667_);
v_size_1668_ = lean_ctor_get(v_r_1484_, 0);
v_k_1669_ = lean_ctor_get(v_r_1484_, 1);
v_v_1670_ = lean_ctor_get(v_r_1484_, 2);
v_l_1671_ = lean_ctor_get(v_r_1484_, 3);
lean_inc(v_l_1671_);
v_r_1672_ = lean_ctor_get(v_r_1484_, 4);
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_dec_lt(v_size_1663_, v_size_1668_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1810_; 
lean_inc(v_l_1666_);
lean_inc(v_v_1665_);
lean_inc(v_k_1664_);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; lean_object* v_unused_1812_; lean_object* v_unused_1813_; lean_object* v_unused_1814_; lean_object* v_unused_1815_; 
v_unused_1811_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_l_1483_, 2);
lean_dec(v_unused_1813_);
v_unused_1814_ = lean_ctor_get(v_l_1483_, 1);
lean_dec(v_unused_1814_);
v_unused_1815_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_1815_);
v___x_1676_ = v_l_1483_;
v_isShared_1677_ = v_isSharedCheck_1810_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_l_1483_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1810_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v_tree_1679_; 
v___x_1678_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1664_, v_v_1665_, v_l_1666_, v_r_1667_);
v_tree_1679_ = lean_ctor_get(v___x_1678_, 2);
if (lean_obj_tag(v_tree_1679_) == 0)
{
lean_object* v_k_1680_; lean_object* v_v_1681_; lean_object* v_size_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
lean_inc_ref(v_tree_1679_);
v_k_1680_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_k_1680_);
v_v_1681_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_v_1681_);
lean_dec_ref(v___x_1678_);
v_size_1682_ = lean_ctor_get(v_tree_1679_, 0);
v___x_1683_ = lean_unsigned_to_nat(3u);
v___x_1684_ = lean_nat_mul(v___x_1683_, v_size_1682_);
v___x_1685_ = lean_nat_dec_lt(v___x_1684_, v_size_1668_);
lean_dec(v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_dec(v_l_1671_);
v___x_1686_ = lean_nat_add(v___x_1673_, v_size_1682_);
v___x_1687_ = lean_nat_add(v___x_1686_, v_size_1668_);
lean_dec(v___x_1686_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_r_1484_);
lean_ctor_set(v___x_1676_, 3, v_tree_1679_);
lean_ctor_set(v___x_1676_, 2, v_v_1681_);
lean_ctor_set(v___x_1676_, 1, v_k_1680_);
lean_ctor_set(v___x_1676_, 0, v___x_1687_);
v___x_1689_ = v___x_1676_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1680_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_tree_1679_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_r_1484_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1745_; 
lean_inc(v_r_1672_);
lean_inc(v_v_1670_);
lean_inc(v_k_1669_);
lean_inc(v_size_1668_);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; lean_object* v_unused_1749_; lean_object* v_unused_1750_; 
v_unused_1746_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_r_1484_, 2);
lean_dec(v_unused_1748_);
v_unused_1749_ = lean_ctor_get(v_r_1484_, 1);
lean_dec(v_unused_1749_);
v_unused_1750_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1750_);
v___x_1692_ = v_r_1484_;
v_isShared_1693_ = v_isSharedCheck_1745_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_r_1484_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1745_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_size_1694_; lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v_l_1697_; lean_object* v_r_1698_; lean_object* v_size_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_size_1694_ = lean_ctor_get(v_l_1671_, 0);
v_k_1695_ = lean_ctor_get(v_l_1671_, 1);
v_v_1696_ = lean_ctor_get(v_l_1671_, 2);
v_l_1697_ = lean_ctor_get(v_l_1671_, 3);
v_r_1698_ = lean_ctor_get(v_l_1671_, 4);
v_size_1699_ = lean_ctor_get(v_r_1672_, 0);
v___x_1700_ = lean_unsigned_to_nat(2u);
v___x_1701_ = lean_nat_mul(v___x_1700_, v_size_1699_);
v___x_1702_ = lean_nat_dec_lt(v_size_1694_, v___x_1701_);
lean_dec(v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1730_; 
lean_inc(v_r_1698_);
lean_inc(v_l_1697_);
lean_inc(v_v_1696_);
lean_inc(v_k_1695_);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_l_1671_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1731_ = lean_ctor_get(v_l_1671_, 4);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_l_1671_, 3);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_l_1671_, 2);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1671_, 1);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1671_, 0);
lean_dec(v_unused_1735_);
v___x_1704_ = v_l_1671_;
v_isShared_1705_ = v_isSharedCheck_1730_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_l_1671_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1730_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1720_; 
v___x_1706_ = lean_nat_add(v___x_1673_, v_size_1682_);
v___x_1707_ = lean_nat_add(v___x_1706_, v_size_1668_);
lean_dec(v_size_1668_);
if (lean_obj_tag(v_l_1697_) == 0)
{
lean_object* v_size_1728_; 
v_size_1728_ = lean_ctor_get(v_l_1697_, 0);
lean_inc(v_size_1728_);
v___y_1720_ = v_size_1728_;
goto v___jp_1719_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_unsigned_to_nat(0u);
v___y_1720_ = v___x_1729_;
goto v___jp_1719_;
}
v___jp_1708_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_nat_add(v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 4, v_r_1672_);
lean_ctor_set(v___x_1704_, 3, v_r_1698_);
lean_ctor_set(v___x_1704_, 2, v_v_1670_);
lean_ctor_set(v___x_1704_, 1, v_k_1669_);
lean_ctor_set(v___x_1704_, 0, v___x_1712_);
v___x_1714_ = v___x_1704_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_r_1698_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_r_1672_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 4, v___x_1714_);
lean_ctor_set(v___x_1692_, 3, v___y_1709_);
lean_ctor_set(v___x_1692_, 2, v_v_1696_);
lean_ctor_set(v___x_1692_, 1, v_k_1695_);
lean_ctor_set(v___x_1692_, 0, v___x_1707_);
v___x_1716_ = v___x_1692_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v___y_1709_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
v___jp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_nat_add(v___x_1706_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec(v___x_1706_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_l_1697_);
lean_ctor_set(v___x_1676_, 3, v_tree_1679_);
lean_ctor_set(v___x_1676_, 2, v_v_1681_);
lean_ctor_set(v___x_1676_, 1, v_k_1680_);
lean_ctor_set(v___x_1676_, 0, v___x_1721_);
v___x_1723_ = v___x_1676_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_k_1680_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_v_1681_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_tree_1679_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_l_1697_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_nat_add(v___x_1673_, v_size_1699_);
if (lean_obj_tag(v_r_1698_) == 0)
{
lean_object* v_size_1725_; 
v_size_1725_ = lean_ctor_get(v_r_1698_, 0);
lean_inc(v_size_1725_);
v___y_1709_ = v___x_1723_;
v___y_1710_ = v___x_1724_;
v___y_1711_ = v_size_1725_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_unsigned_to_nat(0u);
v___y_1709_ = v___x_1723_;
v___y_1710_ = v___x_1724_;
v___y_1711_ = v___x_1726_;
goto v___jp_1708_;
}
}
}
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1736_ = lean_nat_add(v___x_1673_, v_size_1682_);
v___x_1737_ = lean_nat_add(v___x_1736_, v_size_1668_);
lean_dec(v_size_1668_);
v___x_1738_ = lean_nat_add(v___x_1736_, v_size_1694_);
lean_dec(v___x_1736_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 4, v_l_1671_);
lean_ctor_set(v___x_1692_, 3, v_tree_1679_);
lean_ctor_set(v___x_1692_, 2, v_v_1681_);
lean_ctor_set(v___x_1692_, 1, v_k_1680_);
lean_ctor_set(v___x_1692_, 0, v___x_1738_);
v___x_1740_ = v___x_1692_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_k_1680_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_v_1681_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_tree_1679_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_l_1671_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_r_1672_);
lean_ctor_set(v___x_1676_, 3, v___x_1740_);
lean_ctor_set(v___x_1676_, 2, v_v_1670_);
lean_ctor_set(v___x_1676_, 1, v_k_1669_);
lean_ctor_set(v___x_1676_, 0, v___x_1737_);
v___x_1742_ = v___x_1676_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_r_1672_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
else
{
lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1804_; 
lean_inc(v_r_1672_);
lean_inc(v_v_1670_);
lean_inc(v_k_1669_);
lean_inc(v_size_1668_);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; 
v_unused_1805_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_r_1484_, 2);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_r_1484_, 1);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1809_);
v___x_1752_ = v_r_1484_;
v_isShared_1753_ = v_isSharedCheck_1804_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v_r_1484_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1804_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
if (lean_obj_tag(v_l_1671_) == 0)
{
if (lean_obj_tag(v_r_1672_) == 0)
{
lean_object* v_k_1754_; lean_object* v_v_1755_; lean_object* v_size_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
lean_inc(v_tree_1679_);
v_k_1754_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_k_1754_);
v_v_1755_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_v_1755_);
lean_dec_ref(v___x_1678_);
v_size_1756_ = lean_ctor_get(v_l_1671_, 0);
v___x_1757_ = lean_nat_add(v___x_1673_, v_size_1668_);
lean_dec(v_size_1668_);
v___x_1758_ = lean_nat_add(v___x_1673_, v_size_1756_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 4, v_l_1671_);
lean_ctor_set(v___x_1752_, 3, v_tree_1679_);
lean_ctor_set(v___x_1752_, 2, v_v_1755_);
lean_ctor_set(v___x_1752_, 1, v_k_1754_);
lean_ctor_set(v___x_1752_, 0, v___x_1758_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_k_1754_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_v_1755_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_tree_1679_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_l_1671_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_r_1672_);
lean_ctor_set(v___x_1676_, 3, v___x_1760_);
lean_ctor_set(v___x_1676_, 2, v_v_1670_);
lean_ctor_set(v___x_1676_, 1, v_k_1669_);
lean_ctor_set(v___x_1676_, 0, v___x_1757_);
v___x_1762_ = v___x_1676_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_r_1672_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_k_1765_; lean_object* v_v_1766_; lean_object* v_k_1767_; lean_object* v_v_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_size_1668_);
v_k_1765_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_k_1765_);
v_v_1766_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_v_1766_);
lean_dec_ref(v___x_1678_);
v_k_1767_ = lean_ctor_get(v_l_1671_, 1);
v_v_1768_ = lean_ctor_get(v_l_1671_, 2);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_l_1671_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; lean_object* v_unused_1784_; lean_object* v_unused_1785_; 
v_unused_1783_ = lean_ctor_get(v_l_1671_, 4);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v_l_1671_, 3);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v_l_1671_, 0);
lean_dec(v_unused_1785_);
v___x_1770_ = v_l_1671_;
v_isShared_1771_ = v_isSharedCheck_1782_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_v_1768_);
lean_inc(v_k_1767_);
lean_dec(v_l_1671_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1782_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_unsigned_to_nat(3u);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 4, v_r_1672_);
lean_ctor_set(v___x_1770_, 3, v_r_1672_);
lean_ctor_set(v___x_1770_, 2, v_v_1766_);
lean_ctor_set(v___x_1770_, 1, v_k_1765_);
lean_ctor_set(v___x_1770_, 0, v___x_1673_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_k_1765_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_v_1766_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_r_1672_);
v___x_1774_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 3, v_r_1672_);
lean_ctor_set(v___x_1752_, 0, v___x_1673_);
v___x_1776_ = v___x_1752_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_r_1672_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v___x_1776_);
lean_ctor_set(v___x_1676_, 3, v___x_1774_);
lean_ctor_set(v___x_1676_, 2, v_v_1768_);
lean_ctor_set(v___x_1676_, 1, v_k_1767_);
lean_ctor_set(v___x_1676_, 0, v___x_1772_);
v___x_1778_ = v___x_1676_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_k_1767_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_v_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1672_) == 0)
{
lean_object* v_k_1786_; lean_object* v_v_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec(v_size_1668_);
v_k_1786_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_k_1786_);
v_v_1787_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_v_1787_);
lean_dec_ref(v___x_1678_);
v___x_1788_ = lean_unsigned_to_nat(3u);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 4, v_l_1671_);
lean_ctor_set(v___x_1752_, 2, v_v_1787_);
lean_ctor_set(v___x_1752_, 1, v_k_1786_);
lean_ctor_set(v___x_1752_, 0, v___x_1673_);
v___x_1790_ = v___x_1752_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_k_1786_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_v_1787_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_l_1671_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_l_1671_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v_r_1672_);
lean_ctor_set(v___x_1676_, 3, v___x_1790_);
lean_ctor_set(v___x_1676_, 2, v_v_1670_);
lean_ctor_set(v___x_1676_, 1, v_k_1669_);
lean_ctor_set(v___x_1676_, 0, v___x_1788_);
v___x_1792_ = v___x_1676_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v_r_1672_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_k_1795_; lean_object* v_v_1796_; lean_object* v___x_1798_; 
v_k_1795_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_k_1795_);
v_v_1796_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_v_1796_);
lean_dec_ref(v___x_1678_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 3, v_r_1672_);
v___x_1798_ = v___x_1752_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_size_1668_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1803_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1803_, 4, v_r_1672_);
v___x_1798_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = lean_unsigned_to_nat(2u);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 4, v___x_1798_);
lean_ctor_set(v___x_1676_, 3, v_r_1672_);
lean_ctor_set(v___x_1676_, 2, v_v_1796_);
lean_ctor_set(v___x_1676_, 1, v_k_1795_);
lean_ctor_set(v___x_1676_, 0, v___x_1799_);
v___x_1801_ = v___x_1676_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_k_1795_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_v_1796_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_r_1672_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v___x_1798_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
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
lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1968_; 
lean_inc(v_r_1672_);
lean_inc(v_v_1670_);
lean_inc(v_k_1669_);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_r_1484_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; lean_object* v_unused_1973_; 
v_unused_1969_ = lean_ctor_get(v_r_1484_, 4);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_r_1484_, 3);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_r_1484_, 2);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_r_1484_, 1);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_r_1484_, 0);
lean_dec(v_unused_1973_);
v___x_1817_ = v_r_1484_;
v_isShared_1818_ = v_isSharedCheck_1968_;
goto v_resetjp_1816_;
}
else
{
lean_dec(v_r_1484_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1968_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v_tree_1820_; 
v___x_1819_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1669_, v_v_1670_, v_l_1671_, v_r_1672_);
v_tree_1820_ = lean_ctor_get(v___x_1819_, 2);
lean_inc(v_tree_1820_);
if (lean_obj_tag(v_tree_1820_) == 0)
{
lean_object* v_k_1821_; lean_object* v_v_1822_; lean_object* v_size_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_k_1821_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_k_1821_);
v_v_1822_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_v_1822_);
lean_dec_ref(v___x_1819_);
v_size_1823_ = lean_ctor_get(v_tree_1820_, 0);
v___x_1824_ = lean_unsigned_to_nat(3u);
v___x_1825_ = lean_nat_mul(v___x_1824_, v_size_1823_);
v___x_1826_ = lean_nat_dec_lt(v___x_1825_, v_size_1663_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec(v_r_1667_);
v___x_1827_ = lean_nat_add(v___x_1673_, v_size_1663_);
v___x_1828_ = lean_nat_add(v___x_1827_, v_size_1823_);
lean_dec(v___x_1827_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_tree_1820_);
lean_ctor_set(v___x_1817_, 3, v_l_1483_);
lean_ctor_set(v___x_1817_, 2, v_v_1822_);
lean_ctor_set(v___x_1817_, 1, v_k_1821_);
lean_ctor_set(v___x_1817_, 0, v___x_1828_);
v___x_1830_ = v___x_1817_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_k_1821_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_v_1822_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_tree_1820_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1897_; 
lean_inc(v_l_1666_);
lean_inc(v_v_1665_);
lean_inc(v_k_1664_);
lean_inc(v_size_1663_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1898_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_l_1483_, 2);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_l_1483_, 1);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_1902_);
v___x_1833_ = v_l_1483_;
v_isShared_1834_ = v_isSharedCheck_1897_;
goto v_resetjp_1832_;
}
else
{
lean_dec(v_l_1483_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1897_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_size_1835_; lean_object* v_size_1836_; lean_object* v_k_1837_; lean_object* v_v_1838_; lean_object* v_l_1839_; lean_object* v_r_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_size_1835_ = lean_ctor_get(v_l_1666_, 0);
v_size_1836_ = lean_ctor_get(v_r_1667_, 0);
v_k_1837_ = lean_ctor_get(v_r_1667_, 1);
v_v_1838_ = lean_ctor_get(v_r_1667_, 2);
v_l_1839_ = lean_ctor_get(v_r_1667_, 3);
v_r_1840_ = lean_ctor_get(v_r_1667_, 4);
v___x_1841_ = lean_unsigned_to_nat(2u);
v___x_1842_ = lean_nat_mul(v___x_1841_, v_size_1835_);
v___x_1843_ = lean_nat_dec_lt(v_size_1836_, v___x_1842_);
lean_dec(v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1881_; 
lean_inc(v_r_1840_);
lean_inc(v_l_1839_);
lean_inc(v_v_1838_);
lean_inc(v_k_1837_);
lean_del_object(v___x_1833_);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_r_1667_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1882_ = lean_ctor_get(v_r_1667_, 4);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_r_1667_, 3);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_r_1667_, 2);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_r_1667_, 1);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_r_1667_, 0);
lean_dec(v_unused_1886_);
v___x_1845_ = v_r_1667_;
v_isShared_1846_ = v_isSharedCheck_1881_;
goto v_resetjp_1844_;
}
else
{
lean_dec(v_r_1667_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1881_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___x_1869_; lean_object* v___y_1871_; 
v___x_1847_ = lean_nat_add(v___x_1673_, v_size_1663_);
lean_dec(v_size_1663_);
v___x_1848_ = lean_nat_add(v___x_1847_, v_size_1823_);
lean_dec(v___x_1847_);
v___x_1869_ = lean_nat_add(v___x_1673_, v_size_1835_);
if (lean_obj_tag(v_l_1839_) == 0)
{
lean_object* v_size_1879_; 
v_size_1879_ = lean_ctor_get(v_l_1839_, 0);
lean_inc(v_size_1879_);
v___y_1871_ = v_size_1879_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___y_1871_ = v___x_1880_;
goto v___jp_1870_;
}
v___jp_1849_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_nat_add(v___y_1850_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec(v___y_1850_);
lean_inc_ref(v_tree_1820_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 4, v_tree_1820_);
lean_ctor_set(v___x_1845_, 3, v_r_1840_);
lean_ctor_set(v___x_1845_, 2, v_v_1822_);
lean_ctor_set(v___x_1845_, 1, v_k_1821_);
lean_ctor_set(v___x_1845_, 0, v___x_1853_);
v___x_1855_ = v___x_1845_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_k_1821_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_v_1822_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_r_1840_);
lean_ctor_set(v_reuseFailAlloc_1868_, 4, v_tree_1820_);
v___x_1855_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_isSharedCheck_1862_ = !lean_is_exclusive(v_tree_1820_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; 
v_unused_1863_ = lean_ctor_get(v_tree_1820_, 4);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_tree_1820_, 3);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_tree_1820_, 2);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_tree_1820_, 1);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_tree_1820_, 0);
lean_dec(v_unused_1867_);
v___x_1857_ = v_tree_1820_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_dec(v_tree_1820_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 4, v___x_1855_);
lean_ctor_set(v___x_1857_, 3, v___y_1851_);
lean_ctor_set(v___x_1857_, 2, v_v_1838_);
lean_ctor_set(v___x_1857_, 1, v_k_1837_);
lean_ctor_set(v___x_1857_, 0, v___x_1848_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_k_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_v_1838_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v___y_1851_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v___x_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
v___jp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_nat_add(v___x_1869_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec(v___x_1869_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_l_1839_);
lean_ctor_set(v___x_1817_, 3, v_l_1666_);
lean_ctor_set(v___x_1817_, 2, v_v_1665_);
lean_ctor_set(v___x_1817_, 1, v_k_1664_);
lean_ctor_set(v___x_1817_, 0, v___x_1872_);
v___x_1874_ = v___x_1817_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v_l_1839_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_nat_add(v___x_1673_, v_size_1823_);
if (lean_obj_tag(v_r_1840_) == 0)
{
lean_object* v_size_1876_; 
v_size_1876_ = lean_ctor_get(v_r_1840_, 0);
lean_inc(v_size_1876_);
v___y_1850_ = v___x_1875_;
v___y_1851_ = v___x_1874_;
v___y_1852_ = v_size_1876_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___y_1850_ = v___x_1875_;
v___y_1851_ = v___x_1874_;
v___y_1852_ = v___x_1877_;
goto v___jp_1849_;
}
}
}
}
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1887_ = lean_nat_add(v___x_1673_, v_size_1663_);
lean_dec(v_size_1663_);
v___x_1888_ = lean_nat_add(v___x_1887_, v_size_1823_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_nat_add(v___x_1673_, v_size_1823_);
v___x_1890_ = lean_nat_add(v___x_1889_, v_size_1836_);
lean_dec(v___x_1889_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_tree_1820_);
lean_ctor_set(v___x_1817_, 3, v_r_1667_);
lean_ctor_set(v___x_1817_, 2, v_v_1822_);
lean_ctor_set(v___x_1817_, 1, v_k_1821_);
lean_ctor_set(v___x_1817_, 0, v___x_1890_);
v___x_1892_ = v___x_1817_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1821_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1822_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_r_1667_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_tree_1820_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v___x_1892_);
lean_ctor_set(v___x_1833_, 0, v___x_1888_);
v___x_1894_ = v___x_1833_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1666_) == 0)
{
lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1926_; 
lean_inc_ref(v_l_1666_);
lean_inc(v_v_1665_);
lean_inc(v_k_1664_);
lean_inc(v_size_1663_);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; lean_object* v_unused_1928_; lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1927_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_1927_);
v_unused_1928_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_l_1483_, 2);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_l_1483_, 1);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_1931_);
v___x_1904_ = v_l_1483_;
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
else
{
lean_dec(v_l_1483_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_r_1667_) == 0)
{
lean_object* v_k_1906_; lean_object* v_v_1907_; lean_object* v_size_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v_k_1906_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_k_1906_);
v_v_1907_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_v_1907_);
lean_dec_ref(v___x_1819_);
v_size_1908_ = lean_ctor_get(v_r_1667_, 0);
v___x_1909_ = lean_nat_add(v___x_1673_, v_size_1663_);
lean_dec(v_size_1663_);
v___x_1910_ = lean_nat_add(v___x_1673_, v_size_1908_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_tree_1820_);
lean_ctor_set(v___x_1817_, 3, v_r_1667_);
lean_ctor_set(v___x_1817_, 2, v_v_1907_);
lean_ctor_set(v___x_1817_, 1, v_k_1906_);
lean_ctor_set(v___x_1817_, 0, v___x_1910_);
v___x_1912_ = v___x_1817_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_k_1906_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_v_1907_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_r_1667_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_tree_1820_);
v___x_1912_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 4, v___x_1912_);
lean_ctor_set(v___x_1904_, 0, v___x_1909_);
v___x_1914_ = v___x_1904_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_k_1917_; lean_object* v_v_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_dec(v_size_1663_);
v_k_1917_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_k_1917_);
v_v_1918_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_v_1918_);
lean_dec_ref(v___x_1819_);
v___x_1919_ = lean_unsigned_to_nat(3u);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_r_1667_);
lean_ctor_set(v___x_1817_, 3, v_r_1667_);
lean_ctor_set(v___x_1817_, 2, v_v_1918_);
lean_ctor_set(v___x_1817_, 1, v_k_1917_);
lean_ctor_set(v___x_1817_, 0, v___x_1673_);
v___x_1921_ = v___x_1817_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_k_1917_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_v_1918_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_r_1667_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v_r_1667_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 4, v___x_1921_);
lean_ctor_set(v___x_1904_, 0, v___x_1919_);
v___x_1923_ = v___x_1904_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1667_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1956_; 
lean_inc(v_l_1666_);
lean_inc(v_v_1665_);
lean_inc(v_k_1664_);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; lean_object* v_unused_1958_; lean_object* v_unused_1959_; lean_object* v_unused_1960_; lean_object* v_unused_1961_; 
v_unused_1957_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_l_1483_, 2);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_l_1483_, 1);
lean_dec(v_unused_1960_);
v_unused_1961_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_1961_);
v___x_1933_ = v_l_1483_;
v_isShared_1934_ = v_isSharedCheck_1956_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v_l_1483_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1956_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_k_1935_; lean_object* v_v_1936_; lean_object* v_k_1937_; lean_object* v_v_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1952_; 
v_k_1935_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_k_1935_);
v_v_1936_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_v_1936_);
lean_dec_ref(v___x_1819_);
v_k_1937_ = lean_ctor_get(v_r_1667_, 1);
v_v_1938_ = lean_ctor_get(v_r_1667_, 2);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_r_1667_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; 
v_unused_1953_ = lean_ctor_get(v_r_1667_, 4);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_r_1667_, 3);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_r_1667_, 0);
lean_dec(v_unused_1955_);
v___x_1940_ = v_r_1667_;
v_isShared_1941_ = v_isSharedCheck_1952_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_v_1938_);
lean_inc(v_k_1937_);
lean_dec(v_r_1667_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1952_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(3u);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 4, v_l_1666_);
lean_ctor_set(v___x_1940_, 3, v_l_1666_);
lean_ctor_set(v___x_1940_, 2, v_v_1665_);
lean_ctor_set(v___x_1940_, 1, v_k_1664_);
lean_ctor_set(v___x_1940_, 0, v___x_1673_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_l_1666_);
v___x_1944_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_l_1666_);
lean_ctor_set(v___x_1817_, 3, v_l_1666_);
lean_ctor_set(v___x_1817_, 2, v_v_1936_);
lean_ctor_set(v___x_1817_, 1, v_k_1935_);
lean_ctor_set(v___x_1817_, 0, v___x_1673_);
v___x_1946_ = v___x_1817_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1935_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1936_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_l_1666_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_l_1666_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 4, v___x_1946_);
lean_ctor_set(v___x_1933_, 3, v___x_1944_);
lean_ctor_set(v___x_1933_, 2, v_v_1938_);
lean_ctor_set(v___x_1933_, 1, v_k_1937_);
lean_ctor_set(v___x_1933_, 0, v___x_1942_);
v___x_1948_ = v___x_1933_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
else
{
lean_object* v_k_1962_; lean_object* v_v_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v_k_1962_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_k_1962_);
v_v_1963_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_v_1963_);
lean_dec_ref(v___x_1819_);
v___x_1964_ = lean_unsigned_to_nat(2u);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 4, v_r_1667_);
lean_ctor_set(v___x_1817_, 3, v_l_1483_);
lean_ctor_set(v___x_1817_, 2, v_v_1963_);
lean_ctor_set(v___x_1817_, 1, v_k_1962_);
lean_ctor_set(v___x_1817_, 0, v___x_1964_);
v___x_1966_ = v___x_1817_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_k_1962_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_v_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_r_1667_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
}
else
{
return v_l_1483_;
}
}
else
{
return v_r_1484_;
}
}
default: 
{
lean_object* v_impl_1974_; lean_object* v___x_1975_; 
v_impl_1974_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1479_, v_r_1484_);
v___x_1975_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1974_) == 0)
{
if (lean_obj_tag(v_l_1483_) == 0)
{
lean_object* v_size_1976_; lean_object* v_size_1977_; lean_object* v_k_1978_; lean_object* v_v_1979_; lean_object* v_l_1980_; lean_object* v_r_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_size_1976_ = lean_ctor_get(v_impl_1974_, 0);
v_size_1977_ = lean_ctor_get(v_l_1483_, 0);
v_k_1978_ = lean_ctor_get(v_l_1483_, 1);
v_v_1979_ = lean_ctor_get(v_l_1483_, 2);
v_l_1980_ = lean_ctor_get(v_l_1483_, 3);
v_r_1981_ = lean_ctor_get(v_l_1483_, 4);
lean_inc(v_r_1981_);
v___x_1982_ = lean_unsigned_to_nat(3u);
v___x_1983_ = lean_nat_mul(v___x_1982_, v_size_1976_);
v___x_1984_ = lean_nat_dec_lt(v___x_1983_, v_size_1977_);
lean_dec(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec(v_r_1981_);
v___x_1985_ = lean_nat_add(v___x_1975_, v_size_1977_);
v___x_1986_ = lean_nat_add(v___x_1985_, v_size_1976_);
lean_dec(v___x_1985_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_impl_1974_);
lean_ctor_set(v___x_1486_, 0, v___x_1986_);
v___x_1988_ = v___x_1486_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_impl_1974_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2055_; 
lean_inc(v_l_1980_);
lean_inc(v_v_1979_);
lean_inc(v_k_1978_);
lean_inc(v_size_1977_);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; lean_object* v_unused_2057_; lean_object* v_unused_2058_; lean_object* v_unused_2059_; lean_object* v_unused_2060_; 
v_unused_2056_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_l_1483_, 2);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_l_1483_, 1);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_2060_);
v___x_1991_ = v_l_1483_;
v_isShared_1992_ = v_isSharedCheck_2055_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_l_1483_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2055_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_size_1993_; lean_object* v_size_1994_; lean_object* v_k_1995_; lean_object* v_v_1996_; lean_object* v_l_1997_; lean_object* v_r_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_size_1993_ = lean_ctor_get(v_l_1980_, 0);
v_size_1994_ = lean_ctor_get(v_r_1981_, 0);
v_k_1995_ = lean_ctor_get(v_r_1981_, 1);
v_v_1996_ = lean_ctor_get(v_r_1981_, 2);
v_l_1997_ = lean_ctor_get(v_r_1981_, 3);
v_r_1998_ = lean_ctor_get(v_r_1981_, 4);
v___x_1999_ = lean_unsigned_to_nat(2u);
v___x_2000_ = lean_nat_mul(v___x_1999_, v_size_1993_);
v___x_2001_ = lean_nat_dec_lt(v_size_1994_, v___x_2000_);
lean_dec(v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2030_; 
lean_inc(v_r_1998_);
lean_inc(v_l_1997_);
lean_inc(v_v_1996_);
lean_inc(v_k_1995_);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_r_1981_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; lean_object* v_unused_2035_; 
v_unused_2031_ = lean_ctor_get(v_r_1981_, 4);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1981_, 3);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_1981_, 2);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_r_1981_, 1);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_r_1981_, 0);
lean_dec(v_unused_2035_);
v___x_2003_ = v_r_1981_;
v_isShared_2004_ = v_isSharedCheck_2030_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_r_1981_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2030_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___x_2018_; lean_object* v___y_2020_; 
v___x_2005_ = lean_nat_add(v___x_1975_, v_size_1977_);
lean_dec(v_size_1977_);
v___x_2006_ = lean_nat_add(v___x_2005_, v_size_1976_);
lean_dec(v___x_2005_);
v___x_2018_ = lean_nat_add(v___x_1975_, v_size_1993_);
if (lean_obj_tag(v_l_1997_) == 0)
{
lean_object* v_size_2028_; 
v_size_2028_ = lean_ctor_get(v_l_1997_, 0);
lean_inc(v_size_2028_);
v___y_2020_ = v_size_2028_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_unsigned_to_nat(0u);
v___y_2020_ = v___x_2029_;
goto v___jp_2019_;
}
v___jp_2007_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_nat_add(v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v_impl_1974_);
lean_ctor_set(v___x_2003_, 3, v_r_1998_);
lean_ctor_set(v___x_2003_, 2, v_v_1482_);
lean_ctor_set(v___x_2003_, 1, v_k_1481_);
lean_ctor_set(v___x_2003_, 0, v___x_2011_);
v___x_2013_ = v___x_2003_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_r_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_impl_1974_);
v___x_2013_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v___x_2013_);
lean_ctor_set(v___x_1991_, 3, v___y_2008_);
lean_ctor_set(v___x_1991_, 2, v_v_1996_);
lean_ctor_set(v___x_1991_, 1, v_k_1995_);
lean_ctor_set(v___x_1991_, 0, v___x_2006_);
v___x_2015_ = v___x_1991_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v___y_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
v___jp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_nat_add(v___x_2018_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec(v___x_2018_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_l_1997_);
lean_ctor_set(v___x_1486_, 3, v_l_1980_);
lean_ctor_set(v___x_1486_, 2, v_v_1979_);
lean_ctor_set(v___x_1486_, 1, v_k_1978_);
lean_ctor_set(v___x_1486_, 0, v___x_2021_);
v___x_2023_ = v___x_1486_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_k_1978_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_v_1979_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_l_1980_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v_l_1997_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_nat_add(v___x_1975_, v_size_1976_);
if (lean_obj_tag(v_r_1998_) == 0)
{
lean_object* v_size_2025_; 
v_size_2025_ = lean_ctor_get(v_r_1998_, 0);
lean_inc(v_size_2025_);
v___y_2008_ = v___x_2023_;
v___y_2009_ = v___x_2024_;
v___y_2010_ = v_size_2025_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___y_2008_ = v___x_2023_;
v___y_2009_ = v___x_2024_;
v___y_2010_ = v___x_2026_;
goto v___jp_2007_;
}
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_del_object(v___x_1486_);
v___x_2036_ = lean_nat_add(v___x_1975_, v_size_1977_);
lean_dec(v_size_1977_);
v___x_2037_ = lean_nat_add(v___x_2036_, v_size_1976_);
lean_dec(v___x_2036_);
v___x_2038_ = lean_nat_add(v___x_1975_, v_size_1976_);
v___x_2039_ = lean_nat_add(v___x_2038_, v_size_1994_);
lean_dec(v___x_2038_);
lean_inc_ref(v_impl_1974_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_impl_1974_);
lean_ctor_set(v___x_1991_, 3, v_r_1981_);
lean_ctor_set(v___x_1991_, 2, v_v_1482_);
lean_ctor_set(v___x_1991_, 1, v_k_1481_);
lean_ctor_set(v___x_1991_, 0, v___x_2039_);
v___x_2041_ = v___x_1991_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_r_1981_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_impl_1974_);
v___x_2041_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_isSharedCheck_2048_ = !lean_is_exclusive(v_impl_1974_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2049_ = lean_ctor_get(v_impl_1974_, 4);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_impl_1974_, 3);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_impl_1974_, 2);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_impl_1974_, 1);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_impl_1974_, 0);
lean_dec(v_unused_2053_);
v___x_2043_ = v_impl_1974_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_impl_1974_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v___x_2041_);
lean_ctor_set(v___x_2043_, 3, v_l_1980_);
lean_ctor_set(v___x_2043_, 2, v_v_1979_);
lean_ctor_set(v___x_2043_, 1, v_k_1978_);
lean_ctor_set(v___x_2043_, 0, v___x_2037_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_k_1978_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_v_1979_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_l_1980_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v___x_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v_size_2061_ = lean_ctor_get(v_impl_1974_, 0);
v___x_2062_ = lean_nat_add(v___x_1975_, v_size_2061_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_impl_1974_);
lean_ctor_set(v___x_1486_, 0, v___x_2062_);
v___x_2064_ = v___x_1486_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_impl_1974_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
if (lean_obj_tag(v_l_1483_) == 0)
{
lean_object* v_l_2066_; 
v_l_2066_ = lean_ctor_get(v_l_1483_, 3);
if (lean_obj_tag(v_l_2066_) == 0)
{
lean_object* v_r_2067_; 
lean_inc_ref(v_l_2066_);
v_r_2067_ = lean_ctor_get(v_l_1483_, 4);
lean_inc(v_r_2067_);
if (lean_obj_tag(v_r_2067_) == 0)
{
lean_object* v_size_2068_; lean_object* v_k_2069_; lean_object* v_v_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2083_; 
v_size_2068_ = lean_ctor_get(v_l_1483_, 0);
v_k_2069_ = lean_ctor_get(v_l_1483_, 1);
v_v_2070_ = lean_ctor_get(v_l_1483_, 2);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; lean_object* v_unused_2085_; 
v_unused_2084_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_2085_);
v___x_2072_ = v_l_1483_;
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_v_2070_);
lean_inc(v_k_2069_);
lean_inc(v_size_2068_);
lean_dec(v_l_1483_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_size_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v_size_2074_ = lean_ctor_get(v_r_2067_, 0);
v___x_2075_ = lean_nat_add(v___x_1975_, v_size_2068_);
lean_dec(v_size_2068_);
v___x_2076_ = lean_nat_add(v___x_1975_, v_size_2074_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 4, v_impl_1974_);
lean_ctor_set(v___x_2072_, 3, v_r_2067_);
lean_ctor_set(v___x_2072_, 2, v_v_1482_);
lean_ctor_set(v___x_2072_, 1, v_k_1481_);
lean_ctor_set(v___x_2072_, 0, v___x_2076_);
v___x_2078_ = v___x_2072_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_r_2067_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_impl_1974_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_2078_);
lean_ctor_set(v___x_1486_, 3, v_l_2066_);
lean_ctor_set(v___x_1486_, 2, v_v_2070_);
lean_ctor_set(v___x_1486_, 1, v_k_2069_);
lean_ctor_set(v___x_1486_, 0, v___x_2075_);
v___x_2080_ = v___x_1486_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_k_2086_; lean_object* v_v_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2098_; 
v_k_2086_ = lean_ctor_get(v_l_1483_, 1);
v_v_2087_ = lean_ctor_get(v_l_1483_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; lean_object* v_unused_2100_; lean_object* v_unused_2101_; 
v_unused_2099_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_2101_);
v___x_2089_ = v_l_1483_;
v_isShared_2090_ = v_isSharedCheck_2098_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_v_2087_);
lean_inc(v_k_2086_);
lean_dec(v_l_1483_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2098_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_unsigned_to_nat(3u);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 3, v_r_2067_);
lean_ctor_set(v___x_2089_, 2, v_v_1482_);
lean_ctor_set(v___x_2089_, 1, v_k_1481_);
lean_ctor_set(v___x_2089_, 0, v___x_1975_);
v___x_2093_ = v___x_2089_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_r_2067_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_r_2067_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_2093_);
lean_ctor_set(v___x_1486_, 3, v_l_2066_);
lean_ctor_set(v___x_1486_, 2, v_v_2087_);
lean_ctor_set(v___x_1486_, 1, v_k_2086_);
lean_ctor_set(v___x_1486_, 0, v___x_2091_);
v___x_2095_ = v___x_1486_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2086_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2087_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v_r_2102_; 
v_r_2102_ = lean_ctor_get(v_l_1483_, 4);
lean_inc(v_r_2102_);
if (lean_obj_tag(v_r_2102_) == 0)
{
lean_object* v_k_2103_; lean_object* v_v_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2127_; 
lean_inc(v_l_2066_);
v_k_2103_ = lean_ctor_get(v_l_1483_, 1);
v_v_2104_ = lean_ctor_get(v_l_1483_, 2);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_l_1483_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; 
v_unused_2128_ = lean_ctor_get(v_l_1483_, 4);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_l_1483_, 3);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_l_1483_, 0);
lean_dec(v_unused_2130_);
v___x_2106_ = v_l_1483_;
v_isShared_2107_ = v_isSharedCheck_2127_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_v_2104_);
lean_inc(v_k_2103_);
lean_dec(v_l_1483_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2127_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_k_2108_; lean_object* v_v_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2123_; 
v_k_2108_ = lean_ctor_get(v_r_2102_, 1);
v_v_2109_ = lean_ctor_get(v_r_2102_, 2);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_r_2102_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2124_ = lean_ctor_get(v_r_2102_, 4);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_r_2102_, 3);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_r_2102_, 0);
lean_dec(v_unused_2126_);
v___x_2111_ = v_r_2102_;
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_v_2109_);
lean_inc(v_k_2108_);
lean_dec(v_r_2102_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2113_ = lean_unsigned_to_nat(3u);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 4, v_l_2066_);
lean_ctor_set(v___x_2111_, 3, v_l_2066_);
lean_ctor_set(v___x_2111_, 2, v_v_2104_);
lean_ctor_set(v___x_2111_, 1, v_k_2103_);
lean_ctor_set(v___x_2111_, 0, v___x_1975_);
v___x_2115_ = v___x_2111_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_k_2103_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_v_2104_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_l_2066_);
v___x_2115_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2117_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 4, v_l_2066_);
lean_ctor_set(v___x_2106_, 2, v_v_1482_);
lean_ctor_set(v___x_2106_, 1, v_k_1481_);
lean_ctor_set(v___x_2106_, 0, v___x_1975_);
v___x_2117_ = v___x_2106_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_l_2066_);
lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_l_2066_);
v___x_2117_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_2117_);
lean_ctor_set(v___x_1486_, 3, v___x_2115_);
lean_ctor_set(v___x_1486_, 2, v_v_2109_);
lean_ctor_set(v___x_1486_, 1, v_k_2108_);
lean_ctor_set(v___x_1486_, 0, v___x_2113_);
v___x_2119_ = v___x_1486_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_unsigned_to_nat(2u);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_r_2102_);
lean_ctor_set(v___x_1486_, 0, v___x_2131_);
v___x_2133_ = v___x_1486_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_r_2102_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v___x_2136_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_l_1483_);
lean_ctor_set(v___x_1486_, 0, v___x_1975_);
v___x_2136_ = v___x_1486_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_l_1483_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v_l_1483_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
else
{
return v_t_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_2140_, lean_object* v_t_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2140_, v_t_2141_);
lean_dec_ref(v_k_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(lean_object* v_val_2143_, lean_object* v_s_2144_){
_start:
{
lean_object* v_toRingState_2145_; lean_object* v_denoteEntries_2146_; lean_object* v_nextId_2147_; lean_object* v_steps_2148_; lean_object* v_queue_2149_; lean_object* v_basis_2150_; lean_object* v_diseqs_2151_; uint8_t v_recheck_2152_; lean_object* v_invSet_2153_; lean_object* v_powIdentityVarCount_2154_; lean_object* v_numEq0_x3f_2155_; uint8_t v_numEq0Updated_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_toRingState_2145_ = lean_ctor_get(v_s_2144_, 0);
v_denoteEntries_2146_ = lean_ctor_get(v_s_2144_, 1);
v_nextId_2147_ = lean_ctor_get(v_s_2144_, 2);
v_steps_2148_ = lean_ctor_get(v_s_2144_, 3);
v_queue_2149_ = lean_ctor_get(v_s_2144_, 4);
v_basis_2150_ = lean_ctor_get(v_s_2144_, 5);
v_diseqs_2151_ = lean_ctor_get(v_s_2144_, 6);
v_recheck_2152_ = lean_ctor_get_uint8(v_s_2144_, sizeof(void*)*10);
v_invSet_2153_ = lean_ctor_get(v_s_2144_, 7);
v_powIdentityVarCount_2154_ = lean_ctor_get(v_s_2144_, 8);
v_numEq0_x3f_2155_ = lean_ctor_get(v_s_2144_, 9);
v_numEq0Updated_2156_ = lean_ctor_get_uint8(v_s_2144_, sizeof(void*)*10 + 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_s_2144_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2158_ = v_s_2144_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_numEq0_x3f_2155_);
lean_inc(v_powIdentityVarCount_2154_);
lean_inc(v_invSet_2153_);
lean_inc(v_diseqs_2151_);
lean_inc(v_basis_2150_);
lean_inc(v_queue_2149_);
lean_inc(v_steps_2148_);
lean_inc(v_nextId_2147_);
lean_inc(v_denoteEntries_2146_);
lean_inc(v_toRingState_2145_);
lean_dec(v_s_2144_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_2143_, v_queue_2149_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 4, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_toRingState_2145_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_denoteEntries_2146_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_nextId_2147_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_steps_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 5, v_basis_2150_);
lean_ctor_set(v_reuseFailAlloc_2163_, 6, v_diseqs_2151_);
lean_ctor_set(v_reuseFailAlloc_2163_, 7, v_invSet_2153_);
lean_ctor_set(v_reuseFailAlloc_2163_, 8, v_powIdentityVarCount_2154_);
lean_ctor_set(v_reuseFailAlloc_2163_, 9, v_numEq0_x3f_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*10, v_recheck_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*10 + 1, v_numEq0Updated_2156_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed(lean_object* v_val_2165_, lean_object* v_s_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0(v_val_2165_, v_s_2166_);
lean_dec_ref(v_val_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2212_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2212_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2212_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_queue_2177_; lean_object* v___x_2178_; 
v_queue_2177_ = lean_ctor_get(v_a_2173_, 4);
lean_inc(v_queue_2177_);
lean_dec(v_a_2173_);
v___x_2178_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_2177_);
lean_dec(v_queue_2177_);
if (lean_obj_tag(v___x_2178_) == 1)
{
lean_object* v_val_2179_; lean_object* v___f_2180_; lean_object* v___x_2181_; 
lean_del_object(v___x_2175_);
v_val_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2179_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2180_, 0, v_val_2179_);
v___x_2181_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2180_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref_known(v___x_2181_, 1);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2182_, v_a_2169_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; 
v_unused_2191_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2191_);
v___x_2185_ = v___x_2183_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v___x_2183_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2178_);
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2178_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref_known(v___x_2178_, 1);
v_a_2192_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2183_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2183_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref_known(v___x_2178_, 1);
v_a_2200_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2181_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2181_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v___x_2178_);
v___x_2208_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2208_);
v___x_2210_ = v___x_2175_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2172_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2172_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg___boxed(lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___redArg(v_a_2226_, v_a_2227_, v_a_2235_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2252_, lean_object* v_k_2253_, lean_object* v_t_2254_, lean_object* v_h_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2253_, v_t_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2257_, lean_object* v_k_2258_, lean_object* v_t_2259_, lean_object* v_h_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2257_, v_k_2258_, v_t_2259_, v_h_2260_);
lean_dec_ref(v_k_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_){
_start:
{
lean_object* v_ks_2266_; lean_object* v_vs_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2293_; 
v_ks_2266_ = lean_ctor_get(v_x_2262_, 0);
v_vs_2267_ = lean_ctor_get(v_x_2262_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2262_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2269_ = v_x_2262_;
v_isShared_2270_ = v_isSharedCheck_2293_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_vs_2267_);
lean_inc(v_ks_2266_);
lean_dec(v_x_2262_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2293_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_array_get_size(v_ks_2266_);
v___x_2272_ = lean_nat_dec_lt(v_x_2263_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_dec(v_x_2263_);
v___x_2273_ = lean_array_push(v_ks_2266_, v_x_2264_);
v___x_2274_ = lean_array_push(v_vs_2267_, v_x_2265_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v___x_2274_);
lean_ctor_set(v___x_2269_, 0, v___x_2273_);
v___x_2276_ = v___x_2269_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
lean_object* v_k_x27_2278_; size_t v___x_2279_; size_t v___x_2280_; uint8_t v___x_2281_; 
v_k_x27_2278_ = lean_array_fget_borrowed(v_ks_2266_, v_x_2263_);
v___x_2279_ = lean_ptr_addr(v_x_2264_);
v___x_2280_ = lean_ptr_addr(v_k_x27_2278_);
v___x_2281_ = lean_usize_dec_eq(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2283_; 
if (v_isShared_2270_ == 0)
{
v___x_2283_ = v___x_2269_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_ks_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_vs_2267_);
v___x_2283_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_add(v_x_2263_, v___x_2284_);
lean_dec(v_x_2263_);
v_x_2262_ = v___x_2283_;
v_x_2263_ = v___x_2285_;
goto _start;
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2288_ = lean_array_fset(v_ks_2266_, v_x_2263_, v_x_2264_);
v___x_2289_ = lean_array_fset(v_vs_2267_, v_x_2263_, v_x_2265_);
lean_dec(v_x_2263_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v___x_2289_);
lean_ctor_set(v___x_2269_, 0, v___x_2288_);
v___x_2291_ = v___x_2269_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2294_, lean_object* v_k_2295_, lean_object* v_v_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2294_, v___x_2297_, v_k_2295_, v_v_2296_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2300_, size_t v_x_2301_, size_t v_x_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
if (lean_obj_tag(v_x_2300_) == 0)
{
lean_object* v_es_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v_j_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_es_2305_ = lean_ctor_get(v_x_2300_, 0);
v___x_2306_ = ((size_t)31ULL);
v___x_2307_ = lean_usize_land(v_x_2301_, v___x_2306_);
v_j_2308_ = lean_usize_to_nat(v___x_2307_);
v___x_2309_ = lean_array_get_size(v_es_2305_);
v___x_2310_ = lean_nat_dec_lt(v_j_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec(v_j_2308_);
lean_dec(v_x_2304_);
lean_dec_ref(v_x_2303_);
return v_x_2300_;
}
else
{
lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2351_; 
lean_inc_ref(v_es_2305_);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2300_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_x_2300_, 0);
lean_dec(v_unused_2352_);
v___x_2312_ = v_x_2300_;
v_isShared_2313_ = v_isSharedCheck_2351_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v_x_2300_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2351_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_v_2314_; lean_object* v___x_2315_; lean_object* v_xs_x27_2316_; lean_object* v___y_2318_; 
v_v_2314_ = lean_array_fget(v_es_2305_, v_j_2308_);
v___x_2315_ = lean_box(0);
v_xs_x27_2316_ = lean_array_fset(v_es_2305_, v_j_2308_, v___x_2315_);
switch(lean_obj_tag(v_v_2314_))
{
case 0:
{
lean_object* v_key_2323_; lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2336_; 
v_key_2323_ = lean_ctor_get(v_v_2314_, 0);
v_val_2324_ = lean_ctor_get(v_v_2314_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_v_2314_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2326_ = v_v_2314_;
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_inc(v_key_2323_);
lean_dec(v_v_2314_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2336_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
size_t v___x_2328_; size_t v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_ptr_addr(v_x_2303_);
v___x_2329_ = lean_ptr_addr(v_key_2323_);
v___x_2330_ = lean_usize_dec_eq(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_del_object(v___x_2326_);
v___x_2331_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2323_, v_val_2324_, v_x_2303_, v_x_2304_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___y_2318_ = v___x_2332_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2334_; 
lean_dec(v_val_2324_);
lean_dec(v_key_2323_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 1, v_x_2304_);
lean_ctor_set(v___x_2326_, 0, v_x_2303_);
v___x_2334_ = v___x_2326_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_x_2303_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_x_2304_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
v___y_2318_ = v___x_2334_;
goto v___jp_2317_;
}
}
}
}
case 1:
{
lean_object* v_node_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
v_node_2337_ = lean_ctor_get(v_v_2314_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_v_2314_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2339_ = v_v_2314_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_node_2337_);
lean_dec(v_v_2314_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
size_t v___x_2341_; size_t v___x_2342_; size_t v___x_2343_; size_t v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2341_ = ((size_t)5ULL);
v___x_2342_ = lean_usize_shift_right(v_x_2301_, v___x_2341_);
v___x_2343_ = ((size_t)1ULL);
v___x_2344_ = lean_usize_add(v_x_2302_, v___x_2343_);
v___x_2345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2337_, v___x_2342_, v___x_2344_, v_x_2303_, v_x_2304_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2345_);
v___x_2347_ = v___x_2339_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
v___y_2318_ = v___x_2347_;
goto v___jp_2317_;
}
}
}
default: 
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_x_2303_);
lean_ctor_set(v___x_2350_, 1, v_x_2304_);
v___y_2318_ = v___x_2350_;
goto v___jp_2317_;
}
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_array_fset(v_xs_x27_2316_, v_j_2308_, v___y_2318_);
lean_dec(v_j_2308_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2319_);
v___x_2321_ = v___x_2312_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
else
{
lean_object* v_ks_2353_; lean_object* v_vs_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2372_; 
v_ks_2353_ = lean_ctor_get(v_x_2300_, 0);
v_vs_2354_ = lean_ctor_get(v_x_2300_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2300_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2356_ = v_x_2300_;
v_isShared_2357_ = v_isSharedCheck_2372_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_vs_2354_);
lean_inc(v_ks_2353_);
lean_dec(v_x_2300_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2372_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_ks_2353_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_vs_2354_);
v___x_2359_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v_newNode_2360_; size_t v___x_2361_; uint8_t v___x_2362_; 
v_newNode_2360_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2359_, v_x_2303_, v_x_2304_);
v___x_2361_ = ((size_t)7ULL);
v___x_2362_ = lean_usize_dec_le(v___x_2361_, v_x_2302_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2363_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2360_);
v___x_2364_ = lean_unsigned_to_nat(4u);
v___x_2365_ = lean_nat_dec_lt(v___x_2363_, v___x_2364_);
lean_dec(v___x_2363_);
if (v___x_2365_ == 0)
{
lean_object* v_ks_2366_; lean_object* v_vs_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_ks_2366_ = lean_ctor_get(v_newNode_2360_, 0);
lean_inc_ref(v_ks_2366_);
v_vs_2367_ = lean_ctor_get(v_newNode_2360_, 1);
lean_inc_ref(v_vs_2367_);
lean_dec_ref(v_newNode_2360_);
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2369_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2302_, v_ks_2366_, v_vs_2367_, v___x_2368_, v___x_2369_);
lean_dec_ref(v_vs_2367_);
lean_dec_ref(v_ks_2366_);
return v___x_2370_;
}
else
{
return v_newNode_2360_;
}
}
else
{
return v_newNode_2360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_i_2376_, lean_object* v_entries_2377_){
_start:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = lean_array_get_size(v_keys_2374_);
v___x_2379_ = lean_nat_dec_lt(v_i_2376_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_dec(v_i_2376_);
return v_entries_2377_;
}
else
{
lean_object* v_k_2380_; lean_object* v_v_2381_; size_t v___x_2382_; size_t v___x_2383_; size_t v___x_2384_; uint64_t v___x_2385_; size_t v_h_2386_; size_t v___x_2387_; lean_object* v___x_2388_; size_t v___x_2389_; size_t v___x_2390_; size_t v___x_2391_; size_t v_h_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_k_2380_ = lean_array_fget_borrowed(v_keys_2374_, v_i_2376_);
v_v_2381_ = lean_array_fget_borrowed(v_vals_2375_, v_i_2376_);
v___x_2382_ = lean_ptr_addr(v_k_2380_);
v___x_2383_ = ((size_t)3ULL);
v___x_2384_ = lean_usize_shift_right(v___x_2382_, v___x_2383_);
v___x_2385_ = lean_usize_to_uint64(v___x_2384_);
v_h_2386_ = lean_uint64_to_usize(v___x_2385_);
v___x_2387_ = ((size_t)5ULL);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = ((size_t)1ULL);
v___x_2390_ = lean_usize_sub(v_depth_2373_, v___x_2389_);
v___x_2391_ = lean_usize_mul(v___x_2387_, v___x_2390_);
v_h_2392_ = lean_usize_shift_right(v_h_2386_, v___x_2391_);
v___x_2393_ = lean_nat_add(v_i_2376_, v___x_2388_);
lean_dec(v_i_2376_);
lean_inc(v_v_2381_);
lean_inc(v_k_2380_);
v___x_2394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2377_, v_h_2392_, v_depth_2373_, v_k_2380_, v_v_2381_);
v_i_2376_ = v___x_2393_;
v_entries_2377_ = v___x_2394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2396_, lean_object* v_keys_2397_, lean_object* v_vals_2398_, lean_object* v_i_2399_, lean_object* v_entries_2400_){
_start:
{
size_t v_depth_boxed_2401_; lean_object* v_res_2402_; 
v_depth_boxed_2401_ = lean_unbox_usize(v_depth_2396_);
lean_dec(v_depth_2396_);
v_res_2402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2401_, v_keys_2397_, v_vals_2398_, v_i_2399_, v_entries_2400_);
lean_dec_ref(v_vals_2398_);
lean_dec_ref(v_keys_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
size_t v_x_6465__boxed_2408_; size_t v_x_6466__boxed_2409_; lean_object* v_res_2410_; 
v_x_6465__boxed_2408_ = lean_unbox_usize(v_x_2404_);
lean_dec(v_x_2404_);
v_x_6466__boxed_2409_ = lean_unbox_usize(v_x_2405_);
lean_dec(v_x_2405_);
v_res_2410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2403_, v_x_6465__boxed_2408_, v_x_6466__boxed_2409_, v_x_2406_, v_x_2407_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
size_t v___x_2414_; size_t v___x_2415_; size_t v___x_2416_; uint64_t v___x_2417_; size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2414_ = lean_ptr_addr(v_x_2412_);
v___x_2415_ = ((size_t)3ULL);
v___x_2416_ = lean_usize_shift_right(v___x_2414_, v___x_2415_);
v___x_2417_ = lean_usize_to_uint64(v___x_2416_);
v___x_2418_ = lean_uint64_to_usize(v___x_2417_);
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2411_, v___x_2418_, v___x_2419_, v_x_2412_, v_x_2413_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2421_, lean_object* v_ringId_2422_, lean_object* v_s_2423_){
_start:
{
lean_object* v_rings_2424_; lean_object* v_exprToRingId_2425_; lean_object* v_semirings_2426_; lean_object* v_exprToSemiringId_2427_; lean_object* v_ncRings_2428_; lean_object* v_exprToNCRingId_2429_; lean_object* v_ncSemirings_2430_; lean_object* v_exprToNCSemiringId_2431_; lean_object* v_steps_2432_; uint8_t v_reportedMaxDegreeIssue_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
v_rings_2424_ = lean_ctor_get(v_s_2423_, 0);
v_exprToRingId_2425_ = lean_ctor_get(v_s_2423_, 1);
v_semirings_2426_ = lean_ctor_get(v_s_2423_, 2);
v_exprToSemiringId_2427_ = lean_ctor_get(v_s_2423_, 3);
v_ncRings_2428_ = lean_ctor_get(v_s_2423_, 4);
v_exprToNCRingId_2429_ = lean_ctor_get(v_s_2423_, 5);
v_ncSemirings_2430_ = lean_ctor_get(v_s_2423_, 6);
v_exprToNCSemiringId_2431_ = lean_ctor_get(v_s_2423_, 7);
v_steps_2432_ = lean_ctor_get(v_s_2423_, 8);
v_reportedMaxDegreeIssue_2433_ = lean_ctor_get_uint8(v_s_2423_, sizeof(void*)*9);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_s_2423_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2435_ = v_s_2423_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_steps_2432_);
lean_inc(v_exprToNCSemiringId_2431_);
lean_inc(v_ncSemirings_2430_);
lean_inc(v_exprToNCRingId_2429_);
lean_inc(v_ncRings_2428_);
lean_inc(v_exprToSemiringId_2427_);
lean_inc(v_semirings_2426_);
lean_inc(v_exprToRingId_2425_);
lean_inc(v_rings_2424_);
lean_dec(v_s_2423_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2425_, v_e_2421_, v_ringId_2422_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 1, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_rings_2424_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_semirings_2426_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_exprToSemiringId_2427_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_ncRings_2428_);
lean_ctor_set(v_reuseFailAlloc_2440_, 5, v_exprToNCRingId_2429_);
lean_ctor_set(v_reuseFailAlloc_2440_, 6, v_ncSemirings_2430_);
lean_ctor_set(v_reuseFailAlloc_2440_, 7, v_exprToNCSemiringId_2431_);
lean_ctor_set(v_reuseFailAlloc_2440_, 8, v_steps_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2440_, sizeof(void*)*9, v_reportedMaxDegreeIssue_2433_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2444_ = l_Lean_stringToMessageData(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_ringId_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; 
v_ringId_2458_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_ringId_2458_);
lean_inc_ref(v_e_2445_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2459_, 0, v_e_2445_);
lean_closure_set(v___f_2459_, 1, v_ringId_2458_);
v___x_2460_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2445_, v_a_2447_, v_a_2452_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
if (lean_obj_tag(v_a_2461_) == 1)
{
lean_object* v_val_2462_; uint8_t v___x_2463_; 
lean_dec_ref(v___f_2459_);
v_val_2462_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v_a_2461_, 1);
v___x_2463_ = lean_nat_dec_eq(v_val_2462_, v_ringId_2458_);
lean_dec(v_val_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2465_ = l_Lean_indentExpr(v_e_2445_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2448_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; uint8_t v_verbose_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v_verbose_2469_ = lean_ctor_get_uint8(v_a_2468_, 0);
lean_dec(v_a_2468_);
if (v_verbose_2469_ == 0)
{
lean_dec_ref_known(v___x_2466_, 2);
goto v___jp_2455_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Meta_Sym_reportIssue(v___x_2466_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_dec_ref_known(v___x_2470_, 1);
goto v___jp_2455_;
}
else
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref_known(v___x_2466_, 2);
v_a_2471_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2467_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2467_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_dec_ref(v_e_2445_);
goto v___jp_2455_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_a_2461_);
lean_dec_ref(v_e_2445_);
v___x_2479_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2480_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2479_, v___f_2459_, v_a_2447_);
return v___x_2480_;
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v___f_2459_);
lean_dec_ref(v_e_2445_);
v_a_2481_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2460_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2460_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
v___jp_2455_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2500_, v_a_2501_, v_a_2502_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2528_, lean_object* v_x_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2529_, v_x_2530_, v_x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2533_, lean_object* v_x_2534_, size_t v_x_2535_, size_t v_x_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2534_, v_x_2535_, v_x_2536_, v_x_2537_, v_x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
size_t v_x_6751__boxed_2546_; size_t v_x_6752__boxed_2547_; lean_object* v_res_2548_; 
v_x_6751__boxed_2546_ = lean_unbox_usize(v_x_2542_);
lean_dec(v_x_2542_);
v_x_6752__boxed_2547_ = lean_unbox_usize(v_x_2543_);
lean_dec(v_x_2543_);
v_res_2548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2540_, v_x_2541_, v_x_6751__boxed_2546_, v_x_6752__boxed_2547_, v_x_2544_, v_x_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2549_, lean_object* v_n_2550_, lean_object* v_k_2551_, lean_object* v_v_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2550_, v_k_2551_, v_v_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2554_, size_t v_depth_2555_, lean_object* v_keys_2556_, lean_object* v_vals_2557_, lean_object* v_heq_2558_, lean_object* v_i_2559_, lean_object* v_entries_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2555_, v_keys_2556_, v_vals_2557_, v_i_2559_, v_entries_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2562_, lean_object* v_depth_2563_, lean_object* v_keys_2564_, lean_object* v_vals_2565_, lean_object* v_heq_2566_, lean_object* v_i_2567_, lean_object* v_entries_2568_){
_start:
{
size_t v_depth_boxed_2569_; lean_object* v_res_2570_; 
v_depth_boxed_2569_ = lean_unbox_usize(v_depth_2563_);
lean_dec(v_depth_2563_);
v_res_2570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2562_, v_depth_boxed_2569_, v_keys_2564_, v_vals_2565_, v_heq_2566_, v_i_2567_, v_entries_2568_);
lean_dec_ref(v_vals_2565_);
lean_dec_ref(v_keys_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2572_, v_x_2573_, v_x_2574_, v_x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2577_, lean_object* v___f_2578_, lean_object* v___f_2579_, lean_object* v_size_2580_, lean_object* v_s_2581_){
_start:
{
lean_object* v_vars_2582_; lean_object* v_varMap_2583_; lean_object* v_denote_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2593_; 
v_vars_2582_ = lean_ctor_get(v_s_2581_, 0);
v_varMap_2583_ = lean_ctor_get(v_s_2581_, 1);
v_denote_2584_ = lean_ctor_get(v_s_2581_, 2);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_s_2581_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2586_ = v_s_2581_;
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_denote_2584_);
lean_inc(v_varMap_2583_);
lean_inc(v_vars_2582_);
lean_dec(v_s_2581_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_inc_ref(v_e_2577_);
v___x_2588_ = l_Lean_PersistentArray_push___redArg(v_vars_2582_, v_e_2577_);
v___x_2589_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2578_, v___f_2579_, v_varMap_2583_, v_e_2577_, v_size_2580_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 1, v___x_2589_);
lean_ctor_set(v___x_2586_, 0, v___x_2588_);
v___x_2591_ = v___x_2586_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_denote_2584_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2594_, lean_object* v_size_2595_, lean_object* v_____r_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_apply_2(v_toPure_2594_, lean_box(0), v_size_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2598_, lean_object* v_inst_2599_, lean_object* v_toBind_2600_, lean_object* v___f_2601_, lean_object* v_____r_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2604_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2604_, 0, lean_box(0));
lean_closure_set(v___x_2604_, 1, v___x_2603_);
lean_closure_set(v___x_2604_, 2, v_e_2598_);
v___x_2605_ = lean_apply_2(v_inst_2599_, lean_box(0), v___x_2604_);
v___x_2606_ = lean_apply_4(v_toBind_2600_, lean_box(0), lean_box(0), v___x_2605_, v___f_2601_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2607_, lean_object* v_e_2608_, lean_object* v_toBind_2609_, lean_object* v___f_2610_, lean_object* v_____r_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_apply_1(v_inst_2607_, v_e_2608_);
v___x_2613_ = lean_apply_4(v_toBind_2609_, lean_box(0), lean_box(0), v___x_2612_, v___f_2610_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2614_, lean_object* v___f_2615_, lean_object* v_e_2616_, lean_object* v_toPure_2617_, lean_object* v_inst_2618_, lean_object* v_toBind_2619_, lean_object* v_inst_2620_, lean_object* v_modifyRingState_2621_, lean_object* v_s_2622_){
_start:
{
lean_object* v_vars_2623_; lean_object* v_varMap_2624_; lean_object* v___x_2625_; 
v_vars_2623_ = lean_ctor_get(v_s_2622_, 0);
lean_inc_ref(v_vars_2623_);
v_varMap_2624_ = lean_ctor_get(v_s_2622_, 1);
lean_inc_ref(v_varMap_2624_);
lean_dec_ref(v_s_2622_);
lean_inc_ref(v_e_2616_);
lean_inc_ref(v___f_2615_);
lean_inc_ref(v___f_2614_);
v___x_2625_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2614_, v___f_2615_, v_varMap_2624_, v_e_2616_);
lean_dec_ref(v_varMap_2624_);
if (lean_obj_tag(v___x_2625_) == 1)
{
lean_object* v_val_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_vars_2623_);
lean_dec(v_modifyRingState_2621_);
lean_dec(v_inst_2620_);
lean_dec(v_toBind_2619_);
lean_dec(v_inst_2618_);
lean_dec_ref(v_e_2616_);
lean_dec_ref(v___f_2615_);
lean_dec_ref(v___f_2614_);
v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_val_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = lean_apply_2(v_toPure_2617_, lean_box(0), v_val_2626_);
return v___x_2627_;
}
else
{
lean_object* v_size_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v___x_2625_);
v_size_2628_ = lean_ctor_get(v_vars_2623_, 2);
lean_inc_n(v_size_2628_, 2);
lean_dec_ref(v_vars_2623_);
lean_inc_ref_n(v_e_2616_, 2);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2629_, 0, v_e_2616_);
lean_closure_set(v___f_2629_, 1, v___f_2614_);
lean_closure_set(v___f_2629_, 2, v___f_2615_);
lean_closure_set(v___f_2629_, 3, v_size_2628_);
v___f_2630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2630_, 0, v_toPure_2617_);
lean_closure_set(v___f_2630_, 1, v_size_2628_);
lean_inc_n(v_toBind_2619_, 2);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2631_, 0, v_e_2616_);
lean_closure_set(v___f_2631_, 1, v_inst_2618_);
lean_closure_set(v___f_2631_, 2, v_toBind_2619_);
lean_closure_set(v___f_2631_, 3, v___f_2630_);
v___f_2632_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2632_, 0, v_inst_2620_);
lean_closure_set(v___f_2632_, 1, v_e_2616_);
lean_closure_set(v___f_2632_, 2, v_toBind_2619_);
lean_closure_set(v___f_2632_, 3, v___f_2631_);
v___x_2633_ = lean_apply_1(v_modifyRingState_2621_, v___f_2629_);
v___x_2634_ = lean_apply_4(v_toBind_2619_, lean_box(0), lean_box(0), v___x_2633_, v___f_2632_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_e_2641_){
_start:
{
lean_object* v_toApplicative_2642_; lean_object* v_toBind_2643_; lean_object* v_getRingState_2644_; lean_object* v_modifyRingState_2645_; lean_object* v_toPure_2646_; lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v_toApplicative_2642_ = lean_ctor_get(v_inst_2638_, 0);
lean_inc_ref(v_toApplicative_2642_);
v_toBind_2643_ = lean_ctor_get(v_inst_2638_, 1);
lean_inc_n(v_toBind_2643_, 2);
lean_dec_ref(v_inst_2638_);
v_getRingState_2644_ = lean_ctor_get(v_inst_2639_, 0);
lean_inc(v_getRingState_2644_);
v_modifyRingState_2645_ = lean_ctor_get(v_inst_2639_, 1);
lean_inc(v_modifyRingState_2645_);
lean_dec_ref(v_inst_2639_);
v_toPure_2646_ = lean_ctor_get(v_toApplicative_2642_, 1);
lean_inc(v_toPure_2646_);
lean_dec_ref(v_toApplicative_2642_);
v___f_2647_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2648_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2649_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2649_, 0, v___f_2647_);
lean_closure_set(v___f_2649_, 1, v___f_2648_);
lean_closure_set(v___f_2649_, 2, v_e_2641_);
lean_closure_set(v___f_2649_, 3, v_toPure_2646_);
lean_closure_set(v___f_2649_, 4, v_inst_2637_);
lean_closure_set(v___f_2649_, 5, v_toBind_2643_);
lean_closure_set(v___f_2649_, 6, v_inst_2640_);
lean_closure_set(v___f_2649_, 7, v_modifyRingState_2645_);
v___x_2650_ = lean_apply_4(v_toBind_2643_, lean_box(0), lean_box(0), v_getRingState_2644_, v___f_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_e_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2652_, v_inst_2653_, v_inst_2654_, v_inst_2655_, v_e_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2658_, v___y_2659_, v___y_2660_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(lean_object* v___f_2688_, lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v___f_2691_, lean_object* v_e_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2692_, v___y_2694_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; uint8_t v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = lean_unbox(v_a_2706_);
lean_dec(v_a_2706_);
if (v___x_2707_ == 0)
{
lean_object* v_gen_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_gen_2708_ = lean_ctor_get(v___y_2693_, 1);
v___x_2709_ = lean_box(0);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc(v_gen_2708_);
lean_inc_ref(v_e_2692_);
v___x_2710_ = lean_grind_internalize(v_e_2692_, v_gen_2708_, v___x_2709_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_3338__overap_2711_; lean_object* v___x_2712_; 
lean_dec_ref_known(v___x_2710_, 1);
v___x_3338__overap_2711_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2688_, v___x_2689_, v___x_2690_, v___f_2691_, v_e_2692_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2712_ = lean_apply_12(v___x_3338__overap_2711_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
return v___x_2712_;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_e_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___x_2690_);
lean_dec_ref(v___x_2689_);
lean_dec(v___f_2688_);
v_a_2713_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2710_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2710_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v___x_3342__overap_2721_; lean_object* v___x_2722_; 
v___x_3342__overap_2721_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v___f_2688_, v___x_2689_, v___x_2690_, v___f_2691_, v_e_2692_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
v___x_2722_ = lean_apply_12(v___x_3342__overap_2721_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
return v___x_2722_;
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v_e_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___x_2690_);
lean_dec_ref(v___x_2689_);
lean_dec(v___f_2688_);
v_a_2723_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2705_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2705_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed(lean_object** _args){
lean_object* v___f_2731_ = _args[0];
lean_object* v___x_2732_ = _args[1];
lean_object* v___x_2733_ = _args[2];
lean_object* v___f_2734_ = _args[3];
lean_object* v_e_2735_ = _args[4];
lean_object* v___y_2736_ = _args[5];
lean_object* v___y_2737_ = _args[6];
lean_object* v___y_2738_ = _args[7];
lean_object* v___y_2739_ = _args[8];
lean_object* v___y_2740_ = _args[9];
lean_object* v___y_2741_ = _args[10];
lean_object* v___y_2742_ = _args[11];
lean_object* v___y_2743_ = _args[12];
lean_object* v___y_2744_ = _args[13];
lean_object* v___y_2745_ = _args[14];
lean_object* v___y_2746_ = _args[15];
lean_object* v___y_2747_ = _args[16];
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0(v___f_2731_, v___x_2732_, v___x_2733_, v___f_2734_, v_e_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2748_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0(void){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_instMonadEIO___redArg();
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__0);
v___x_2751_ = l_StateRefT_x27_instMonad___redArg(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM(void){
_start:
{
lean_object* v___x_2761_; lean_object* v_toApplicative_2762_; lean_object* v_toFunctor_2763_; lean_object* v_toSeq_2764_; lean_object* v_toSeqLeft_2765_; lean_object* v_toSeqRight_2766_; lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___f_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; lean_object* v___f_2773_; lean_object* v___f_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v_toApplicative_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2825_; 
v___x_2761_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__1);
v_toApplicative_2762_ = lean_ctor_get(v___x_2761_, 0);
v_toFunctor_2763_ = lean_ctor_get(v_toApplicative_2762_, 0);
v_toSeq_2764_ = lean_ctor_get(v_toApplicative_2762_, 2);
v_toSeqLeft_2765_ = lean_ctor_get(v_toApplicative_2762_, 3);
v_toSeqRight_2766_ = lean_ctor_get(v_toApplicative_2762_, 4);
v___f_2767_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__2));
v___f_2768_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__3));
lean_inc_ref_n(v_toFunctor_2763_, 2);
v___f_2769_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2769_, 0, v_toFunctor_2763_);
v___f_2770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2770_, 0, v_toFunctor_2763_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___f_2769_);
lean_ctor_set(v___x_2771_, 1, v___f_2770_);
lean_inc(v_toSeqRight_2766_);
v___f_2772_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2772_, 0, v_toSeqRight_2766_);
lean_inc(v_toSeqLeft_2765_);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2773_, 0, v_toSeqLeft_2765_);
lean_inc(v_toSeq_2764_);
v___f_2774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2774_, 0, v_toSeq_2764_);
v___x_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2771_);
lean_ctor_set(v___x_2775_, 1, v___f_2767_);
lean_ctor_set(v___x_2775_, 2, v___f_2774_);
lean_ctor_set(v___x_2775_, 3, v___f_2773_);
lean_ctor_set(v___x_2775_, 4, v___f_2772_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v___f_2768_);
v___x_2777_ = l_StateRefT_x27_instMonad___redArg(v___x_2776_);
v_toApplicative_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2777_, 1);
lean_dec(v_unused_2826_);
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2825_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_toApplicative_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2825_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v_toFunctor_2782_; lean_object* v_toSeq_2783_; lean_object* v_toSeqLeft_2784_; lean_object* v_toSeqRight_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2823_; 
v_toFunctor_2782_ = lean_ctor_get(v_toApplicative_2778_, 0);
v_toSeq_2783_ = lean_ctor_get(v_toApplicative_2778_, 2);
v_toSeqLeft_2784_ = lean_ctor_get(v_toApplicative_2778_, 3);
v_toSeqRight_2785_ = lean_ctor_get(v_toApplicative_2778_, 4);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_toApplicative_2778_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_toApplicative_2778_, 1);
lean_dec(v_unused_2824_);
v___x_2787_ = v_toApplicative_2778_;
v_isShared_2788_ = v_isSharedCheck_2823_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_toSeqRight_2785_);
lean_inc(v_toSeqLeft_2784_);
lean_inc(v_toSeq_2783_);
lean_inc(v_toFunctor_2782_);
lean_dec(v_toApplicative_2778_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2823_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___f_2794_; lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___x_2798_; 
v___f_2789_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__4));
v___f_2790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__5));
lean_inc_ref(v_toFunctor_2782_);
v___f_2791_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2791_, 0, v_toFunctor_2782_);
v___f_2792_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2792_, 0, v_toFunctor_2782_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___f_2791_);
lean_ctor_set(v___x_2793_, 1, v___f_2792_);
v___f_2794_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2794_, 0, v_toSeqRight_2785_);
v___f_2795_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2795_, 0, v_toSeqLeft_2784_);
v___f_2796_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2796_, 0, v_toSeq_2783_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 4, v___f_2794_);
lean_ctor_set(v___x_2787_, 3, v___f_2795_);
lean_ctor_set(v___x_2787_, 2, v___f_2796_);
lean_ctor_set(v___x_2787_, 1, v___f_2789_);
lean_ctor_set(v___x_2787_, 0, v___x_2793_);
v___x_2798_ = v___x_2787_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___f_2789_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v___f_2796_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v___f_2795_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v___f_2794_);
v___x_2798_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v___f_2790_);
lean_ctor_set(v___x_2780_, 0, v___x_2798_);
v___x_2800_ = v___x_2780_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___f_2790_);
v___x_2800_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_toApplicative_2809_; lean_object* v_toBind_2810_; lean_object* v_getCommRingState_2811_; lean_object* v_modifyCommRingState_2812_; lean_object* v_toPure_2813_; lean_object* v___f_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___f_2819_; lean_object* v___f_2820_; 
v___x_2801_ = l_StateRefT_x27_instMonad___redArg(v___x_2800_);
v___x_2802_ = l_ReaderT_instMonad___redArg(v___x_2801_);
v___x_2803_ = l_StateRefT_x27_instMonad___redArg(v___x_2802_);
v___x_2804_ = l_ReaderT_instMonad___redArg(v___x_2803_);
v___x_2805_ = l_ReaderT_instMonad___redArg(v___x_2804_);
v___x_2806_ = l_StateRefT_x27_instMonad___redArg(v___x_2805_);
v___x_2807_ = l_ReaderT_instMonad___redArg(v___x_2806_);
v___x_2808_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateRingM;
v_toApplicative_2809_ = lean_ctor_get(v___x_2807_, 0);
v_toBind_2810_ = lean_ctor_get(v___x_2807_, 1);
v_getCommRingState_2811_ = lean_ctor_get(v___x_2808_, 0);
v_modifyCommRingState_2812_ = lean_ctor_get(v___x_2808_, 1);
v_toPure_2813_ = lean_ctor_get(v_toApplicative_2809_, 1);
v___f_2814_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___closed__8));
lean_inc(v_modifyCommRingState_2812_);
v___f_2815_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2815_, 0, v_modifyCommRingState_2812_);
lean_inc(v_toPure_2813_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2816_, 0, v_toPure_2813_);
lean_inc(v_toBind_2810_);
lean_inc(v_getCommRingState_2811_);
v___x_2817_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v_getCommRingState_2811_, v___f_2816_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___f_2815_);
v___f_2819_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0));
v___f_2820_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadMkVarRingM___lam__0___boxed), 17, 4);
lean_closure_set(v___f_2820_, 0, v___f_2814_);
lean_closure_set(v___f_2820_, 1, v___x_2807_);
lean_closure_set(v___f_2820_, 2, v___x_2818_);
lean_closure_set(v___f_2820_, 3, v___f_2819_);
return v___f_2820_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_2827_; lean_object* v_n_2828_; 
v___x_2827_ = lean_unsigned_to_nat(1u);
v_n_2828_ = l_Lean_mkRawNatLit(v___x_2827_);
return v_n_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(lean_object* v_u_2842_, lean_object* v_type_2843_, lean_object* v_semiringInst_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_n_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v_ofNatInst_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_n_2852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
v___x_2853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__5));
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_u_2842_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
lean_inc_ref(v___x_2855_);
v___x_2856_ = l_Lean_mkConst(v___x_2853_, v___x_2855_);
lean_inc_ref(v_type_2843_);
v_ofNatInst_2857_ = l_Lean_mkApp3(v___x_2856_, v_type_2843_, v_semiringInst_2844_, v_n_2852_);
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__7));
v___x_2859_ = l_Lean_mkConst(v___x_2858_, v___x_2855_);
v___x_2860_ = l_Lean_mkApp3(v___x_2859_, v_type_2843_, v_n_2852_, v_ofNatInst_2857_);
v___x_2861_ = l_Lean_Meta_Sym_canon(v___x_2860_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Lean_Meta_Sym_shareCommon(v_a_2862_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2863_;
}
else
{
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___boxed(lean_object* v_u_2864_, lean_object* v_type_2865_, lean_object* v_semiringInst_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_2864_, v_type_2865_, v_semiringInst_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(lean_object* v_u_2875_, lean_object* v_type_2876_, lean_object* v_semiringInst_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_2875_, v_type_2876_, v_semiringInst_2877_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___boxed(lean_object* v_u_2891_, lean_object* v_type_2892_, lean_object* v_semiringInst_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne(v_u_2891_, v_type_2892_, v_semiringInst_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0(lean_object* v_a_2907_, lean_object* v_s_2908_){
_start:
{
lean_object* v_toRing_2909_; lean_object* v_invFn_x3f_2910_; lean_object* v_divFn_x3f_2911_; lean_object* v_semiringId_x3f_2912_; lean_object* v_commSemiringInst_2913_; lean_object* v_commRingInst_2914_; lean_object* v_noZeroDivInst_x3f_2915_; lean_object* v_fieldInst_x3f_2916_; lean_object* v_powIdentityInst_x3f_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2948_; 
v_toRing_2909_ = lean_ctor_get(v_s_2908_, 0);
v_invFn_x3f_2910_ = lean_ctor_get(v_s_2908_, 1);
v_divFn_x3f_2911_ = lean_ctor_get(v_s_2908_, 2);
v_semiringId_x3f_2912_ = lean_ctor_get(v_s_2908_, 3);
v_commSemiringInst_2913_ = lean_ctor_get(v_s_2908_, 4);
v_commRingInst_2914_ = lean_ctor_get(v_s_2908_, 5);
v_noZeroDivInst_x3f_2915_ = lean_ctor_get(v_s_2908_, 6);
v_fieldInst_x3f_2916_ = lean_ctor_get(v_s_2908_, 7);
v_powIdentityInst_x3f_2917_ = lean_ctor_get(v_s_2908_, 8);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_s_2908_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2919_ = v_s_2908_;
v_isShared_2920_ = v_isSharedCheck_2948_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_powIdentityInst_x3f_2917_);
lean_inc(v_fieldInst_x3f_2916_);
lean_inc(v_noZeroDivInst_x3f_2915_);
lean_inc(v_commRingInst_2914_);
lean_inc(v_commSemiringInst_2913_);
lean_inc(v_semiringId_x3f_2912_);
lean_inc(v_divFn_x3f_2911_);
lean_inc(v_invFn_x3f_2910_);
lean_inc(v_toRing_2909_);
lean_dec(v_s_2908_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2948_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_id_2921_; lean_object* v_type_2922_; lean_object* v_u_2923_; lean_object* v_ringInst_2924_; lean_object* v_semiringInst_2925_; lean_object* v_charInst_x3f_2926_; lean_object* v_addFn_x3f_2927_; lean_object* v_mulFn_x3f_2928_; lean_object* v_subFn_x3f_2929_; lean_object* v_negFn_x3f_2930_; lean_object* v_powFn_x3f_2931_; lean_object* v_intCastFn_x3f_2932_; lean_object* v_natCastFn_x3f_2933_; lean_object* v_natSMulFn_x3f_2934_; lean_object* v_intSMulFn_x3f_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2946_; 
v_id_2921_ = lean_ctor_get(v_toRing_2909_, 0);
v_type_2922_ = lean_ctor_get(v_toRing_2909_, 1);
v_u_2923_ = lean_ctor_get(v_toRing_2909_, 2);
v_ringInst_2924_ = lean_ctor_get(v_toRing_2909_, 3);
v_semiringInst_2925_ = lean_ctor_get(v_toRing_2909_, 4);
v_charInst_x3f_2926_ = lean_ctor_get(v_toRing_2909_, 5);
v_addFn_x3f_2927_ = lean_ctor_get(v_toRing_2909_, 6);
v_mulFn_x3f_2928_ = lean_ctor_get(v_toRing_2909_, 7);
v_subFn_x3f_2929_ = lean_ctor_get(v_toRing_2909_, 8);
v_negFn_x3f_2930_ = lean_ctor_get(v_toRing_2909_, 9);
v_powFn_x3f_2931_ = lean_ctor_get(v_toRing_2909_, 10);
v_intCastFn_x3f_2932_ = lean_ctor_get(v_toRing_2909_, 11);
v_natCastFn_x3f_2933_ = lean_ctor_get(v_toRing_2909_, 12);
v_natSMulFn_x3f_2934_ = lean_ctor_get(v_toRing_2909_, 13);
v_intSMulFn_x3f_2935_ = lean_ctor_get(v_toRing_2909_, 14);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_toRing_2909_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v_toRing_2909_, 15);
lean_dec(v_unused_2947_);
v___x_2937_ = v_toRing_2909_;
v_isShared_2938_ = v_isSharedCheck_2946_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_intSMulFn_x3f_2935_);
lean_inc(v_natSMulFn_x3f_2934_);
lean_inc(v_natCastFn_x3f_2933_);
lean_inc(v_intCastFn_x3f_2932_);
lean_inc(v_powFn_x3f_2931_);
lean_inc(v_negFn_x3f_2930_);
lean_inc(v_subFn_x3f_2929_);
lean_inc(v_mulFn_x3f_2928_);
lean_inc(v_addFn_x3f_2927_);
lean_inc(v_charInst_x3f_2926_);
lean_inc(v_semiringInst_2925_);
lean_inc(v_ringInst_2924_);
lean_inc(v_u_2923_);
lean_inc(v_type_2922_);
lean_inc(v_id_2921_);
lean_dec(v_toRing_2909_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2946_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2907_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 15, v___x_2939_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_id_2921_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_type_2922_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_u_2923_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_ringInst_2924_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_semiringInst_2925_);
lean_ctor_set(v_reuseFailAlloc_2945_, 5, v_charInst_x3f_2926_);
lean_ctor_set(v_reuseFailAlloc_2945_, 6, v_addFn_x3f_2927_);
lean_ctor_set(v_reuseFailAlloc_2945_, 7, v_mulFn_x3f_2928_);
lean_ctor_set(v_reuseFailAlloc_2945_, 8, v_subFn_x3f_2929_);
lean_ctor_set(v_reuseFailAlloc_2945_, 9, v_negFn_x3f_2930_);
lean_ctor_set(v_reuseFailAlloc_2945_, 10, v_powFn_x3f_2931_);
lean_ctor_set(v_reuseFailAlloc_2945_, 11, v_intCastFn_x3f_2932_);
lean_ctor_set(v_reuseFailAlloc_2945_, 12, v_natCastFn_x3f_2933_);
lean_ctor_set(v_reuseFailAlloc_2945_, 13, v_natSMulFn_x3f_2934_);
lean_ctor_set(v_reuseFailAlloc_2945_, 14, v_intSMulFn_x3f_2935_);
lean_ctor_set(v_reuseFailAlloc_2945_, 15, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2943_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2941_);
v___x_2943_ = v___x_2919_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_invFn_x3f_2910_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_divFn_x3f_2911_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v_semiringId_x3f_2912_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v_commSemiringInst_2913_);
lean_ctor_set(v_reuseFailAlloc_2944_, 5, v_commRingInst_2914_);
lean_ctor_set(v_reuseFailAlloc_2944_, 6, v_noZeroDivInst_x3f_2915_);
lean_ctor_set(v_reuseFailAlloc_2944_, 7, v_fieldInst_x3f_2916_);
lean_ctor_set(v_reuseFailAlloc_2944_, 8, v_powIdentityInst_x3f_2917_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2949_, lean_object* v_i_2950_, lean_object* v_k_2951_){
_start:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_array_get_size(v_keys_2949_);
v___x_2953_ = lean_nat_dec_lt(v_i_2950_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec(v_i_2950_);
return v___x_2953_;
}
else
{
lean_object* v_k_x27_2954_; size_t v___x_2955_; size_t v___x_2956_; uint8_t v___x_2957_; 
v_k_x27_2954_ = lean_array_fget_borrowed(v_keys_2949_, v_i_2950_);
v___x_2955_ = lean_ptr_addr(v_k_2951_);
v___x_2956_ = lean_ptr_addr(v_k_x27_2954_);
v___x_2957_ = lean_usize_dec_eq(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_add(v_i_2950_, v___x_2958_);
lean_dec(v_i_2950_);
v_i_2950_ = v___x_2959_;
goto _start;
}
else
{
lean_dec(v_i_2950_);
return v___x_2953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2961_, lean_object* v_i_2962_, lean_object* v_k_2963_){
_start:
{
uint8_t v_res_2964_; lean_object* v_r_2965_; 
v_res_2964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_2961_, v_i_2962_, v_k_2963_);
lean_dec_ref(v_k_2963_);
lean_dec_ref(v_keys_2961_);
v_r_2965_ = lean_box(v_res_2964_);
return v_r_2965_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(lean_object* v_x_2966_, size_t v_x_2967_, lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2966_) == 0)
{
lean_object* v_es_2969_; lean_object* v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v_j_2973_; lean_object* v___x_2974_; 
v_es_2969_ = lean_ctor_get(v_x_2966_, 0);
v___x_2970_ = lean_box(2);
v___x_2971_ = ((size_t)31ULL);
v___x_2972_ = lean_usize_land(v_x_2967_, v___x_2971_);
v_j_2973_ = lean_usize_to_nat(v___x_2972_);
v___x_2974_ = lean_array_get_borrowed(v___x_2970_, v_es_2969_, v_j_2973_);
lean_dec(v_j_2973_);
switch(lean_obj_tag(v___x_2974_))
{
case 0:
{
lean_object* v_key_2975_; size_t v___x_2976_; size_t v___x_2977_; uint8_t v___x_2978_; 
v_key_2975_ = lean_ctor_get(v___x_2974_, 0);
v___x_2976_ = lean_ptr_addr(v_x_2968_);
v___x_2977_ = lean_ptr_addr(v_key_2975_);
v___x_2978_ = lean_usize_dec_eq(v___x_2976_, v___x_2977_);
return v___x_2978_;
}
case 1:
{
lean_object* v_node_2979_; size_t v___x_2980_; size_t v___x_2981_; 
v_node_2979_ = lean_ctor_get(v___x_2974_, 0);
v___x_2980_ = ((size_t)5ULL);
v___x_2981_ = lean_usize_shift_right(v_x_2967_, v___x_2980_);
v_x_2966_ = v_node_2979_;
v_x_2967_ = v___x_2981_;
goto _start;
}
default: 
{
uint8_t v___x_2983_; 
v___x_2983_ = 0;
return v___x_2983_;
}
}
}
else
{
lean_object* v_ks_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v_ks_2984_ = lean_ctor_get(v_x_2966_, 0);
v___x_2985_ = lean_unsigned_to_nat(0u);
v___x_2986_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_ks_2984_, v___x_2985_, v_x_2968_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg___boxed(lean_object* v_x_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_){
_start:
{
size_t v_x_9654__boxed_2990_; uint8_t v_res_2991_; lean_object* v_r_2992_; 
v_x_9654__boxed_2990_ = lean_unbox_usize(v_x_2988_);
lean_dec(v_x_2988_);
v_res_2991_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_2987_, v_x_9654__boxed_2990_, v_x_2989_);
lean_dec_ref(v_x_2989_);
lean_dec_ref(v_x_2987_);
v_r_2992_ = lean_box(v_res_2991_);
return v_r_2992_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
size_t v___x_2995_; size_t v___x_2996_; size_t v___x_2997_; uint64_t v___x_2998_; size_t v___x_2999_; uint8_t v___x_3000_; 
v___x_2995_ = lean_ptr_addr(v_x_2994_);
v___x_2996_ = ((size_t)3ULL);
v___x_2997_ = lean_usize_shift_right(v___x_2995_, v___x_2996_);
v___x_2998_ = lean_usize_to_uint64(v___x_2997_);
v___x_2999_ = lean_uint64_to_usize(v___x_2998_);
v___x_3000_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_2993_, v___x_2999_, v_x_2994_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg___boxed(lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
uint8_t v_res_3003_; lean_object* v_r_3004_; 
v_res_3003_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3001_, v_x_3002_);
lean_dec_ref(v_x_3002_);
lean_dec_ref(v_x_3001_);
v_r_3004_ = lean_box(v_res_3003_);
return v_r_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne(lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_one_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v_toRing_3071_; lean_object* v_one_x3f_3072_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v_toRing_3071_ = lean_ctor_get(v_a_3070_, 0);
lean_inc_ref(v_toRing_3071_);
lean_dec(v_a_3070_);
v_one_x3f_3072_ = lean_ctor_get(v_toRing_3071_, 15);
if (lean_obj_tag(v_one_x3f_3072_) == 1)
{
lean_object* v_val_3073_; 
lean_inc_ref(v_one_x3f_3072_);
lean_dec_ref(v_toRing_3071_);
v_val_3073_ = lean_ctor_get(v_one_x3f_3072_, 0);
lean_inc(v_val_3073_);
lean_dec_ref_known(v_one_x3f_3072_, 1);
v_one_3018_ = v_val_3073_;
v___y_3019_ = v_a_3005_;
v___y_3020_ = v_a_3006_;
v___y_3021_ = v_a_3007_;
v___y_3022_ = v_a_3008_;
v___y_3023_ = v_a_3009_;
v___y_3024_ = v_a_3010_;
v___y_3025_ = v_a_3011_;
v___y_3026_ = v_a_3012_;
v___y_3027_ = v_a_3013_;
v___y_3028_ = v_a_3014_;
v___y_3029_ = v_a_3015_;
goto v___jp_3017_;
}
else
{
lean_object* v_type_3074_; lean_object* v_u_3075_; lean_object* v_semiringInst_3076_; lean_object* v___x_3077_; 
v_type_3074_ = lean_ctor_get(v_toRing_3071_, 1);
lean_inc_ref(v_type_3074_);
v_u_3075_ = lean_ctor_get(v_toRing_3071_, 2);
lean_inc(v_u_3075_);
v_semiringInst_3076_ = lean_ctor_get(v_toRing_3071_, 4);
lean_inc_ref(v_semiringInst_3076_);
lean_dec_ref(v_toRing_3071_);
v___x_3077_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_u_3075_, v_type_3074_, v_semiringInst_3076_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_n(v_a_3078_, 2);
lean_dec_ref_known(v___x_3077_, 1);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getOne___lam__0), 2, 1);
lean_closure_set(v___f_3079_, 0, v_a_3078_);
v___x_3080_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3079_, v_a_3005_, v_a_3011_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref_known(v___x_3080_, 1);
v_one_3018_ = v_a_3078_;
v___y_3019_ = v_a_3005_;
v___y_3020_ = v_a_3006_;
v___y_3021_ = v_a_3007_;
v___y_3022_ = v_a_3008_;
v___y_3023_ = v_a_3009_;
v___y_3024_ = v_a_3010_;
v___y_3025_ = v_a_3011_;
v___y_3026_ = v_a_3012_;
v___y_3027_ = v_a_3013_;
v___y_3028_ = v_a_3014_;
v___y_3029_ = v_a_3015_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3078_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
return v___x_3077_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
v_a_3089_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3069_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3069_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
v___jp_3017_:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_3019_, v___y_3020_, v___y_3028_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3060_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3060_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3060_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v_toRingState_3035_; lean_object* v_denote_3036_; uint8_t v___x_3037_; 
v_toRingState_3035_ = lean_ctor_get(v_a_3031_, 0);
lean_inc_ref(v_toRingState_3035_);
lean_dec(v_a_3031_);
v_denote_3036_ = lean_ctor_get(v_toRingState_3035_, 2);
lean_inc_ref(v_denote_3036_);
lean_dec_ref(v_toRingState_3035_);
v___x_3037_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_denote_3036_, v_one_3018_);
lean_dec_ref(v_denote_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_del_object(v___x_3033_);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_box(0);
lean_inc(v___y_3029_);
lean_inc_ref(v___y_3028_);
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc(v___y_3025_);
lean_inc_ref(v___y_3024_);
lean_inc(v___y_3023_);
lean_inc_ref(v___y_3022_);
lean_inc(v___y_3021_);
lean_inc(v___y_3020_);
lean_inc_ref(v_one_3018_);
v___x_3040_ = lean_grind_internalize(v_one_3018_, v___x_3038_, v___x_3039_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3048_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v_one_3018_);
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_one_3018_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_one_3018_);
v_a_3049_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3040_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3040_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v___x_3058_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v_one_3018_);
v___x_3058_ = v___x_3033_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_one_3018_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v_one_3018_);
v_a_3061_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3030_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3030_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getOne___boxed(lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Meta_Grind_Arith_CommRing_getOne(v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
return v_res_3109_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(lean_object* v_00_u03b2_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
uint8_t v___x_3113_; 
v___x_3113_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___redArg(v_x_3111_, v_x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0___boxed(lean_object* v_00_u03b2_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_res_3117_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0(v_00_u03b2_3114_, v_x_3115_, v_x_3116_);
lean_dec_ref(v_x_3116_);
lean_dec_ref(v_x_3115_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(lean_object* v_00_u03b2_3119_, lean_object* v_x_3120_, size_t v_x_3121_, lean_object* v_x_3122_){
_start:
{
uint8_t v___x_3123_; 
v___x_3123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___redArg(v_x_3120_, v_x_3121_, v_x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3124_, lean_object* v_x_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_){
_start:
{
size_t v_x_9875__boxed_3128_; uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_x_9875__boxed_3128_ = lean_unbox_usize(v_x_3126_);
lean_dec(v_x_3126_);
v_res_3129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0(v_00_u03b2_3124_, v_x_3125_, v_x_9875__boxed_3128_, v_x_3127_);
lean_dec_ref(v_x_3127_);
lean_dec_ref(v_x_3125_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3131_, lean_object* v_keys_3132_, lean_object* v_vals_3133_, lean_object* v_heq_3134_, lean_object* v_i_3135_, lean_object* v_k_3136_){
_start:
{
uint8_t v___x_3137_; 
v___x_3137_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___redArg(v_keys_3132_, v_i_3135_, v_k_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3138_, lean_object* v_keys_3139_, lean_object* v_vals_3140_, lean_object* v_heq_3141_, lean_object* v_i_3142_, lean_object* v_k_3143_){
_start:
{
uint8_t v_res_3144_; lean_object* v_r_3145_; 
v_res_3144_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_CommRing_getOne_spec__0_spec__0_spec__1(v_00_u03b2_3138_, v_keys_3139_, v_vals_3140_, v_heq_3141_, v_i_3142_, v_k_3143_);
lean_dec_ref(v_k_3143_);
lean_dec_ref(v_vals_3140_);
lean_dec_ref(v_keys_3139_);
v_r_3145_ = lean_box(v_res_3144_);
return v_r_3145_;
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
