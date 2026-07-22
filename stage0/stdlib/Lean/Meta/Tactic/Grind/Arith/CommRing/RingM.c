// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing import Lean.Meta.Sym.Arith.Poly
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_steps_13_ = lean_ctor_get(v_a_6_, 12);
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
lean_object* v_rings_67_; lean_object* v_typeIdOf_68_; lean_object* v_exprToRingId_69_; lean_object* v_semirings_70_; lean_object* v_stypeIdOf_71_; lean_object* v_exprToSemiringId_72_; lean_object* v_ncRings_73_; lean_object* v_exprToNCRingId_74_; lean_object* v_nctypeIdOf_75_; lean_object* v_ncSemirings_76_; lean_object* v_exprToNCSemiringId_77_; lean_object* v_ncstypeIdOf_78_; lean_object* v_steps_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_rings_67_ = lean_ctor_get(v_s_66_, 0);
v_typeIdOf_68_ = lean_ctor_get(v_s_66_, 1);
v_exprToRingId_69_ = lean_ctor_get(v_s_66_, 2);
v_semirings_70_ = lean_ctor_get(v_s_66_, 3);
v_stypeIdOf_71_ = lean_ctor_get(v_s_66_, 4);
v_exprToSemiringId_72_ = lean_ctor_get(v_s_66_, 5);
v_ncRings_73_ = lean_ctor_get(v_s_66_, 6);
v_exprToNCRingId_74_ = lean_ctor_get(v_s_66_, 7);
v_nctypeIdOf_75_ = lean_ctor_get(v_s_66_, 8);
v_ncSemirings_76_ = lean_ctor_get(v_s_66_, 9);
v_exprToNCSemiringId_77_ = lean_ctor_get(v_s_66_, 10);
v_ncstypeIdOf_78_ = lean_ctor_get(v_s_66_, 11);
v_steps_79_ = lean_ctor_get(v_s_66_, 12);
v_isSharedCheck_86_ = !lean_is_exclusive(v_s_66_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_s_66_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_steps_79_);
lean_inc(v_ncstypeIdOf_78_);
lean_inc(v_exprToNCSemiringId_77_);
lean_inc(v_ncSemirings_76_);
lean_inc(v_nctypeIdOf_75_);
lean_inc(v_exprToNCRingId_74_);
lean_inc(v_ncRings_73_);
lean_inc(v_exprToSemiringId_72_);
lean_inc(v_stypeIdOf_71_);
lean_inc(v_semirings_70_);
lean_inc(v_exprToRingId_69_);
lean_inc(v_typeIdOf_68_);
lean_inc(v_rings_67_);
lean_dec(v_s_66_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_rings_67_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_typeIdOf_68_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_exprToRingId_69_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_semirings_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v_stypeIdOf_71_);
lean_ctor_set(v_reuseFailAlloc_85_, 5, v_exprToSemiringId_72_);
lean_ctor_set(v_reuseFailAlloc_85_, 6, v_ncRings_73_);
lean_ctor_set(v_reuseFailAlloc_85_, 7, v_exprToNCRingId_74_);
lean_ctor_set(v_reuseFailAlloc_85_, 8, v_nctypeIdOf_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 9, v_ncSemirings_76_);
lean_ctor_set(v_reuseFailAlloc_85_, 10, v_exprToNCSemiringId_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 11, v_ncstypeIdOf_78_);
lean_ctor_set(v_reuseFailAlloc_85_, 12, v_steps_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*13, v___x_65_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object* v___x_87_, lean_object* v_s_88_){
_start:
{
uint8_t v___x_7583__boxed_89_; lean_object* v_res_90_; 
v___x_7583__boxed_89_ = lean_unbox(v___x_87_);
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_7583__boxed_89_, v_s_88_);
return v_res_90_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0));
v___x_93_ = l_Lean_stringToMessageData(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2));
v___x_96_ = l_Lean_stringToMessageData(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4));
v___x_99_ = l_Lean_stringToMessageData(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object* v_p_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_102_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_200_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_200_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_ringMaxDegree_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_ringMaxDegree_115_ = lean_ctor_get(v_a_111_, 7);
lean_inc(v_ringMaxDegree_115_);
lean_dec(v_a_111_);
v___x_116_ = l_Lean_Grind_CommRing_Poly_degree(v_p_100_);
v___x_117_ = lean_nat_dec_le(v_ringMaxDegree_115_, v___x_116_);
lean_dec(v_ringMaxDegree_115_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v___x_116_);
v___x_118_ = lean_box(v___x_117_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_118_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_122_; 
lean_del_object(v___x_113_);
v___x_122_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_101_, v_a_107_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_191_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_191_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_191_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_191_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v_reportedMaxDegreeIssue_127_; 
v_reportedMaxDegreeIssue_127_ = lean_ctor_get_uint8(v_a_123_, sizeof(void*)*13);
lean_dec(v_a_123_);
if (v_reportedMaxDegreeIssue_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_125_);
v___x_128_ = lean_box(v___x_117_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
v___x_130_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_131_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_130_, v___f_129_, v_a_101_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; 
lean_dec_ref_known(v___x_131_, 1);
v___x_132_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_103_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_170_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_170_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_170_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_170_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
uint8_t v_verbose_137_; 
v_verbose_137_ = lean_ctor_get_uint8(v_a_133_, 0);
lean_dec(v_a_133_);
if (v_verbose_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v___x_116_);
v___x_138_ = lean_box(v___x_117_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_del_object(v___x_135_);
v___x_142_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
v___x_143_ = l_Nat_reprFast(v___x_116_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = l_Lean_MessageData_ofFormat(v___x_144_);
lean_inc_ref(v___x_145_);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_145_);
v___x_150_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Lean_Meta_Sym_reportIssue(v___x_151_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_152_, 0);
lean_dec(v_unused_161_);
v___x_154_ = v___x_152_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_dec(v___x_152_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_box(v___x_117_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_152_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v___x_116_);
v_a_171_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_132_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_132_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v___x_116_);
v_a_179_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_131_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_131_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_dec(v___x_116_);
v___x_187_ = lean_box(v___x_117_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_187_);
v___x_189_ = v___x_125_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v___x_116_);
v_a_192_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_122_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_122_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_110_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_110_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object* v_p_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_p_209_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object* v_p_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_220_, v_a_221_, v_a_223_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object* v_p_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_p_233_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_246_, lean_object* v_s_247_){
_start:
{
lean_object* v_rings_248_; lean_object* v_typeIdOf_249_; lean_object* v_exprToRingId_250_; lean_object* v_semirings_251_; lean_object* v_stypeIdOf_252_; lean_object* v_exprToSemiringId_253_; lean_object* v_ncRings_254_; lean_object* v_exprToNCRingId_255_; lean_object* v_nctypeIdOf_256_; lean_object* v_ncSemirings_257_; lean_object* v_exprToNCSemiringId_258_; lean_object* v_ncstypeIdOf_259_; lean_object* v_steps_260_; uint8_t v_reportedMaxDegreeIssue_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_rings_248_ = lean_ctor_get(v_s_247_, 0);
v_typeIdOf_249_ = lean_ctor_get(v_s_247_, 1);
v_exprToRingId_250_ = lean_ctor_get(v_s_247_, 2);
v_semirings_251_ = lean_ctor_get(v_s_247_, 3);
v_stypeIdOf_252_ = lean_ctor_get(v_s_247_, 4);
v_exprToSemiringId_253_ = lean_ctor_get(v_s_247_, 5);
v_ncRings_254_ = lean_ctor_get(v_s_247_, 6);
v_exprToNCRingId_255_ = lean_ctor_get(v_s_247_, 7);
v_nctypeIdOf_256_ = lean_ctor_get(v_s_247_, 8);
v_ncSemirings_257_ = lean_ctor_get(v_s_247_, 9);
v_exprToNCSemiringId_258_ = lean_ctor_get(v_s_247_, 10);
v_ncstypeIdOf_259_ = lean_ctor_get(v_s_247_, 11);
v_steps_260_ = lean_ctor_get(v_s_247_, 12);
v_reportedMaxDegreeIssue_261_ = lean_ctor_get_uint8(v_s_247_, sizeof(void*)*13);
v_isSharedCheck_269_ = !lean_is_exclusive(v_s_247_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_s_247_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_steps_260_);
lean_inc(v_ncstypeIdOf_259_);
lean_inc(v_exprToNCSemiringId_258_);
lean_inc(v_ncSemirings_257_);
lean_inc(v_nctypeIdOf_256_);
lean_inc(v_exprToNCRingId_255_);
lean_inc(v_ncRings_254_);
lean_inc(v_exprToSemiringId_253_);
lean_inc(v_stypeIdOf_252_);
lean_inc(v_semirings_251_);
lean_inc(v_exprToRingId_250_);
lean_inc(v_typeIdOf_249_);
lean_inc(v_rings_248_);
lean_dec(v_s_247_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_nat_add(v_steps_260_, v_n_246_);
lean_dec(v_steps_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 12, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_rings_248_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_typeIdOf_249_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_exprToRingId_250_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_semirings_251_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_stypeIdOf_252_);
lean_ctor_set(v_reuseFailAlloc_268_, 5, v_exprToSemiringId_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 6, v_ncRings_254_);
lean_ctor_set(v_reuseFailAlloc_268_, 7, v_exprToNCRingId_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 8, v_nctypeIdOf_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 9, v_ncSemirings_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 10, v_exprToNCSemiringId_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 11, v_ncstypeIdOf_259_);
lean_ctor_set(v_reuseFailAlloc_268_, 12, v___x_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_268_, sizeof(void*)*13, v_reportedMaxDegreeIssue_261_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_270_, lean_object* v_s_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_270_, v_s_271_);
lean_dec(v_n_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_276_, 0, v_n_273_);
v___x_277_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_277_, v___f_276_, v_a_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_279_, v_a_280_);
lean_dec(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_283_, v_a_284_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_309_, lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = 0;
v___x_323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_323_, 0, v_ringId_309_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_322_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc(v_a_311_);
v___x_324_ = lean_apply_12(v_x_310_, v___x_323_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_325_, lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_325_, v_x_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_339_, lean_object* v_ringId_340_, lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = 0;
v___x_354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_354_, 0, v_ringId_340_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_353_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
lean_inc(v_a_343_);
lean_inc(v_a_342_);
v___x_355_ = lean_apply_12(v_x_341_, v___x_354_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_356_, lean_object* v_ringId_357_, lean_object* v_x_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_356_, v_ringId_357_, v_x_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_371_){
_start:
{
lean_object* v_ringId_373_; lean_object* v___x_374_; 
v_ringId_373_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_ringId_373_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_ringId_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_375_);
lean_dec_ref(v_a_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_ringId_390_; lean_object* v___x_391_; 
v_ringId_390_ = lean_ctor_get(v_a_378_, 0);
lean_inc(v_ringId_390_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_ringId_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_canon(v_e_405_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_Sym_shareCommon(v_a_419_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_420_;
}
else
{
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_435_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_mctx_478_; lean_object* v_lctx_479_; lean_object* v_options_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v___y_471_);
v_mctx_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_mctx_478_);
lean_dec(v___x_477_);
v_lctx_479_ = lean_ctor_get(v___y_470_, 2);
v_options_480_ = lean_ctor_get(v___y_472_, 2);
lean_inc_ref(v_options_480_);
lean_inc_ref(v_lctx_479_);
v___x_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_481_, 0, v_env_476_);
lean_ctor_set(v___x_481_, 1, v_mctx_478_);
lean_ctor_set(v___x_481_, 2, v_lctx_479_);
lean_ctor_set(v___x_481_, 3, v_options_480_);
v___x_482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_msgData_469_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_ref_497_ = lean_ctor_get(v___y_494_, 5);
v___x_498_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_ref_497_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_497_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_519_, v_a_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_545_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_545_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_ringId_535_; lean_object* v_rings_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_ringId_535_ = lean_ctor_get(v_a_518_, 0);
v_rings_536_ = lean_ctor_get(v_a_531_, 0);
lean_inc_ref(v_rings_536_);
lean_dec(v_a_531_);
v___x_537_ = lean_array_get_size(v_rings_536_);
v___x_538_ = lean_nat_dec_lt(v_ringId_535_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_rings_536_);
lean_del_object(v___x_533_);
v___x_539_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_540_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_539_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_fget(v_rings_536_, v_ringId_535_);
lean_dec_ref(v_rings_536_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_541_);
v___x_543_ = v___x_533_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_530_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_530_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
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
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_567_, lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_568_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_582_, lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_582_, v_msg_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_597_, lean_object* v_f_598_, lean_object* v_s_599_){
_start:
{
lean_object* v_rings_600_; lean_object* v_typeIdOf_601_; lean_object* v_exprToRingId_602_; lean_object* v_semirings_603_; lean_object* v_stypeIdOf_604_; lean_object* v_exprToSemiringId_605_; lean_object* v_ncRings_606_; lean_object* v_exprToNCRingId_607_; lean_object* v_nctypeIdOf_608_; lean_object* v_ncSemirings_609_; lean_object* v_exprToNCSemiringId_610_; lean_object* v_ncstypeIdOf_611_; lean_object* v_steps_612_; uint8_t v_reportedMaxDegreeIssue_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_rings_600_ = lean_ctor_get(v_s_599_, 0);
v_typeIdOf_601_ = lean_ctor_get(v_s_599_, 1);
v_exprToRingId_602_ = lean_ctor_get(v_s_599_, 2);
v_semirings_603_ = lean_ctor_get(v_s_599_, 3);
v_stypeIdOf_604_ = lean_ctor_get(v_s_599_, 4);
v_exprToSemiringId_605_ = lean_ctor_get(v_s_599_, 5);
v_ncRings_606_ = lean_ctor_get(v_s_599_, 6);
v_exprToNCRingId_607_ = lean_ctor_get(v_s_599_, 7);
v_nctypeIdOf_608_ = lean_ctor_get(v_s_599_, 8);
v_ncSemirings_609_ = lean_ctor_get(v_s_599_, 9);
v_exprToNCSemiringId_610_ = lean_ctor_get(v_s_599_, 10);
v_ncstypeIdOf_611_ = lean_ctor_get(v_s_599_, 11);
v_steps_612_ = lean_ctor_get(v_s_599_, 12);
v_reportedMaxDegreeIssue_613_ = lean_ctor_get_uint8(v_s_599_, sizeof(void*)*13);
v___x_614_ = lean_array_get_size(v_rings_600_);
v___x_615_ = lean_nat_dec_lt(v_ringId_597_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec_ref(v_f_598_);
return v_s_599_;
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
lean_inc(v_steps_612_);
lean_inc_ref(v_ncstypeIdOf_611_);
lean_inc_ref(v_exprToNCSemiringId_610_);
lean_inc_ref(v_ncSemirings_609_);
lean_inc_ref(v_nctypeIdOf_608_);
lean_inc_ref(v_exprToNCRingId_607_);
lean_inc_ref(v_ncRings_606_);
lean_inc_ref(v_exprToSemiringId_605_);
lean_inc_ref(v_stypeIdOf_604_);
lean_inc_ref(v_semirings_603_);
lean_inc_ref(v_exprToRingId_602_);
lean_inc_ref(v_typeIdOf_601_);
lean_inc_ref(v_rings_600_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_s_599_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_628_ = lean_ctor_get(v_s_599_, 12);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_s_599_, 11);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_s_599_, 10);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_s_599_, 9);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_s_599_, 8);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_s_599_, 7);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_s_599_, 6);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_s_599_, 5);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_s_599_, 4);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_s_599_, 3);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_s_599_, 2);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_s_599_, 1);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_s_599_, 0);
lean_dec(v_unused_640_);
v___x_617_ = v_s_599_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_s_599_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_v_619_; lean_object* v___x_620_; lean_object* v_xs_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_v_619_ = lean_array_fget(v_rings_600_, v_ringId_597_);
v___x_620_ = lean_box(0);
v_xs_x27_621_ = lean_array_fset(v_rings_600_, v_ringId_597_, v___x_620_);
v___x_622_ = lean_apply_1(v_f_598_, v_v_619_);
v___x_623_ = lean_array_fset(v_xs_x27_621_, v_ringId_597_, v___x_622_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_623_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_typeIdOf_601_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_exprToRingId_602_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_semirings_603_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_stypeIdOf_604_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_exprToSemiringId_605_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_ncRings_606_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_exprToNCRingId_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_nctypeIdOf_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_ncSemirings_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 10, v_exprToNCSemiringId_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 11, v_ncstypeIdOf_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 12, v_steps_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*13, v_reportedMaxDegreeIssue_613_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_641_, lean_object* v_f_642_, lean_object* v_s_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_641_, v_f_642_, v_s_643_);
lean_dec(v_ringId_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_ringId_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_ringId_649_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_ringId_649_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_650_, 0, v_ringId_649_);
lean_closure_set(v___f_650_, 1, v_f_645_);
v___x_651_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_651_, v___f_650_, v_a_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_658_, v_a_659_, v_a_660_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_685_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_ringId_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_ringId_704_ = lean_ctor_get(v_a_692_, 0);
v___x_705_ = 1;
lean_inc(v_ringId_704_);
v___x_706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_706_, 0, v_ringId_704_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*1, v___x_705_);
lean_inc(v_a_702_);
lean_inc_ref(v_a_701_);
lean_inc(v_a_700_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc_ref(v_a_697_);
lean_inc(v_a_696_);
lean_inc_ref(v_a_695_);
lean_inc(v_a_694_);
lean_inc(v_a_693_);
v___x_707_ = lean_apply_12(v_x_691_, v___x_706_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_ringId_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_ringId_736_ = lean_ctor_get(v_a_724_, 0);
v___x_737_ = 1;
lean_inc(v_ringId_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_738_, 0, v_ringId_736_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*1, v___x_737_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc(v_a_732_);
lean_inc_ref(v_a_731_);
lean_inc(v_a_730_);
lean_inc_ref(v_a_729_);
lean_inc(v_a_728_);
lean_inc_ref(v_a_727_);
lean_inc(v_a_726_);
lean_inc(v_a_725_);
v___x_739_ = lean_apply_12(v_x_723_, v___x_738_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, lean_box(0));
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_740_, lean_object* v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_740_, v_x_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_755_){
_start:
{
uint8_t v_checkCoeffDvd_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_checkCoeffDvd_757_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*1);
v___x_758_ = lean_box(v_checkCoeffDvd_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_760_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_763_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_i_791_, lean_object* v_k_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_keys_789_);
v___x_794_ = lean_nat_dec_lt(v_i_791_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_i_791_);
v___x_795_ = lean_box(0);
return v___x_795_;
}
else
{
lean_object* v_k_x27_796_; size_t v___x_797_; size_t v___x_798_; uint8_t v___x_799_; 
v_k_x27_796_ = lean_array_fget_borrowed(v_keys_789_, v_i_791_);
v___x_797_ = lean_ptr_addr(v_k_792_);
v___x_798_ = lean_ptr_addr(v_k_x27_796_);
v___x_799_ = lean_usize_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_add(v_i_791_, v___x_800_);
lean_dec(v_i_791_);
v_i_791_ = v___x_801_;
goto _start;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_array_fget_borrowed(v_vals_790_, v_i_791_);
lean_dec(v_i_791_);
lean_inc(v___x_803_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_805_, lean_object* v_vals_806_, lean_object* v_i_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_805_, v_vals_806_, v_i_807_, v_k_808_);
lean_dec_ref(v_k_808_);
lean_dec_ref(v_vals_806_);
lean_dec_ref(v_keys_805_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_810_, size_t v_x_811_, lean_object* v_x_812_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v_es_813_; lean_object* v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v_j_817_; lean_object* v___x_818_; 
v_es_813_ = lean_ctor_get(v_x_810_, 0);
v___x_814_ = lean_box(2);
v___x_815_ = ((size_t)31ULL);
v___x_816_ = lean_usize_land(v_x_811_, v___x_815_);
v_j_817_ = lean_usize_to_nat(v___x_816_);
v___x_818_ = lean_array_get_borrowed(v___x_814_, v_es_813_, v_j_817_);
lean_dec(v_j_817_);
switch(lean_obj_tag(v___x_818_))
{
case 0:
{
lean_object* v_key_819_; lean_object* v_val_820_; size_t v___x_821_; size_t v___x_822_; uint8_t v___x_823_; 
v_key_819_ = lean_ctor_get(v___x_818_, 0);
v_val_820_ = lean_ctor_get(v___x_818_, 1);
v___x_821_ = lean_ptr_addr(v_x_812_);
v___x_822_ = lean_ptr_addr(v_key_819_);
v___x_823_ = lean_usize_dec_eq(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
v___x_824_ = lean_box(0);
return v___x_824_;
}
else
{
lean_object* v___x_825_; 
lean_inc(v_val_820_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_val_820_);
return v___x_825_;
}
}
case 1:
{
lean_object* v_node_826_; size_t v___x_827_; size_t v___x_828_; 
v_node_826_ = lean_ctor_get(v___x_818_, 0);
v___x_827_ = ((size_t)5ULL);
v___x_828_ = lean_usize_shift_right(v_x_811_, v___x_827_);
v_x_810_ = v_node_826_;
v_x_811_ = v___x_828_;
goto _start;
}
default: 
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
}
else
{
lean_object* v_ks_831_; lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_ks_831_ = lean_ctor_get(v_x_810_, 0);
v_vs_832_ = lean_ctor_get(v_x_810_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_831_, v_vs_832_, v___x_833_, v_x_812_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
size_t v_x_890__boxed_838_; lean_object* v_res_839_; 
v_x_890__boxed_838_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_res_839_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_835_, v_x_890__boxed_838_, v_x_837_);
lean_dec_ref(v_x_837_);
lean_dec_ref(v_x_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; uint64_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_842_ = lean_ptr_addr(v_x_841_);
v___x_843_ = ((size_t)3ULL);
v___x_844_ = lean_usize_shift_right(v___x_842_, v___x_843_);
v___x_845_ = lean_usize_to_uint64(v___x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_840_, v___x_846_, v_x_841_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_848_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_exprToRingId_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v_exprToRingId_860_ = lean_ctor_get(v_a_856_, 2);
lean_inc_ref(v_exprToRingId_860_);
lean_dec(v_a_856_);
v___x_861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_860_, v_e_851_);
lean_dec_ref(v_exprToRingId_860_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_855_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_855_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_874_, v_a_875_, v_a_876_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_e_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_879_, v_a_880_, v_a_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
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
lean_dec_ref(v_e_892_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_909_, v_x_910_, v_x_911_);
lean_dec_ref(v_x_911_);
lean_dec_ref(v_x_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_913_, lean_object* v_x_914_, size_t v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_914_, v_x_915_, v_x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
size_t v_x_1011__boxed_922_; lean_object* v_res_923_; 
v_x_1011__boxed_922_ = lean_unbox_usize(v_x_920_);
lean_dec(v_x_920_);
v_res_923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_918_, v_x_919_, v_x_1011__boxed_922_, v_x_921_);
lean_dec_ref(v_x_921_);
lean_dec_ref(v_x_919_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_k_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_925_, v_vals_926_, v_i_928_, v_k_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_931_, lean_object* v_keys_932_, lean_object* v_vals_933_, lean_object* v_heq_934_, lean_object* v_i_935_, lean_object* v_k_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_931_, v_keys_932_, v_vals_933_, v_heq_934_, v_i_935_, v_k_936_);
lean_dec_ref(v_k_936_);
lean_dec_ref(v_vals_933_);
lean_dec_ref(v_keys_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_938_, lean_object* v_____do__lift_939_){
_start:
{
lean_object* v_charInst_x3f_943_; 
v_charInst_x3f_943_ = lean_ctor_get(v_____do__lift_939_, 5);
lean_inc(v_charInst_x3f_943_);
lean_dec_ref(v_____do__lift_939_);
if (lean_obj_tag(v_charInst_x3f_943_) == 1)
{
lean_object* v_val_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_955_; 
v_val_944_ = lean_ctor_get(v_charInst_x3f_943_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_charInst_x3f_943_);
if (v_isSharedCheck_955_ == 0)
{
v___x_946_ = v_charInst_x3f_943_;
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_val_944_);
lean_dec(v_charInst_x3f_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_snd_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_snd_948_ = lean_ctor_get(v_val_944_, 1);
lean_inc(v_snd_948_);
lean_dec(v_val_944_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_nat_dec_eq(v_snd_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_952_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_snd_948_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_snd_948_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_apply_2(v_toPure_938_, lean_box(0), v___x_952_);
return v___x_953_;
}
}
else
{
lean_dec(v_snd_948_);
lean_del_object(v___x_946_);
goto v___jp_940_;
}
}
}
else
{
lean_dec(v_charInst_x3f_943_);
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_apply_2(v_toPure_938_, lean_box(0), v___x_941_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v_toApplicative_958_; lean_object* v_toBind_959_; lean_object* v_getRing_960_; lean_object* v_toPure_961_; lean_object* v___f_962_; lean_object* v___x_963_; 
v_toApplicative_958_ = lean_ctor_get(v_inst_956_, 0);
lean_inc_ref(v_toApplicative_958_);
v_toBind_959_ = lean_ctor_get(v_inst_956_, 1);
lean_inc(v_toBind_959_);
lean_dec_ref(v_inst_956_);
v_getRing_960_ = lean_ctor_get(v_inst_957_, 0);
lean_inc(v_getRing_960_);
lean_dec_ref(v_inst_957_);
v_toPure_961_ = lean_ctor_get(v_toApplicative_958_, 1);
lean_inc(v_toPure_961_);
lean_dec_ref(v_toApplicative_958_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_962_, 0, v_toPure_961_);
v___x_963_ = lean_apply_4(v_toBind_959_, lean_box(0), lean_box(0), v_getRing_960_, v___f_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_964_, lean_object* v_inst_965_, lean_object* v_inst_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_965_, v_inst_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_968_, lean_object* v_____do__lift_969_){
_start:
{
lean_object* v_charInst_x3f_973_; 
v_charInst_x3f_973_ = lean_ctor_get(v_____do__lift_969_, 5);
lean_inc(v_charInst_x3f_973_);
lean_dec_ref(v_____do__lift_969_);
if (lean_obj_tag(v_charInst_x3f_973_) == 1)
{
lean_object* v_val_974_; lean_object* v_snd_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_val_974_ = lean_ctor_get(v_charInst_x3f_973_, 0);
v_snd_975_ = lean_ctor_get(v_val_974_, 1);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_nat_dec_eq(v_snd_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_apply_2(v_toPure_968_, lean_box(0), v_charInst_x3f_973_);
return v___x_978_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_973_, 1);
goto v___jp_970_;
}
}
else
{
lean_dec(v_charInst_x3f_973_);
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_apply_2(v_toPure_968_, lean_box(0), v___x_971_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_979_, lean_object* v_inst_980_){
_start:
{
lean_object* v_toApplicative_981_; lean_object* v_toBind_982_; lean_object* v_getRing_983_; lean_object* v_toPure_984_; lean_object* v___f_985_; lean_object* v___x_986_; 
v_toApplicative_981_ = lean_ctor_get(v_inst_979_, 0);
lean_inc_ref(v_toApplicative_981_);
v_toBind_982_ = lean_ctor_get(v_inst_979_, 1);
lean_inc(v_toBind_982_);
lean_dec_ref(v_inst_979_);
v_getRing_983_ = lean_ctor_get(v_inst_980_, 0);
lean_inc(v_getRing_983_);
lean_dec_ref(v_inst_980_);
v_toPure_984_ = lean_ctor_get(v_toApplicative_981_, 1);
lean_inc(v_toPure_984_);
lean_dec_ref(v_toApplicative_981_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_985_, 0, v_toPure_984_);
v___x_986_ = lean_apply_4(v_toBind_982_, lean_box(0), lean_box(0), v_getRing_983_, v___f_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_987_, lean_object* v_inst_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_988_, v_inst_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_noZeroDivInst_x3f_1008_; lean_object* v___x_1010_; 
v_noZeroDivInst_x3f_1008_ = lean_ctor_get(v_a_1004_, 5);
lean_inc(v_noZeroDivInst_x3f_1008_);
lean_dec(v_a_1004_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_noZeroDivInst_x3f_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_noZeroDivInst_x3f_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1003_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1003_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1062_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1062_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1062_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_noZeroDivInst_x3f_1051_; 
v_noZeroDivInst_x3f_1051_ = lean_ctor_get(v_a_1047_, 5);
lean_inc(v_noZeroDivInst_x3f_1051_);
lean_dec(v_a_1047_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1051_) == 0)
{
uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = 0;
v___x_1053_ = lean_box(v___x_1052_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1053_);
v___x_1055_ = v___x_1049_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1051_, 1);
v___x_1057_ = 1;
v___x_1058_ = lean_box(v___x_1057_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1058_);
v___x_1060_ = v___x_1049_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1046_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1046_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1113_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_toRing_1101_; lean_object* v_charInst_x3f_1102_; 
v_toRing_1101_ = lean_ctor_get(v_a_1097_, 0);
lean_inc_ref(v_toRing_1101_);
lean_dec(v_a_1097_);
v_charInst_x3f_1102_ = lean_ctor_get(v_toRing_1101_, 5);
lean_inc(v_charInst_x3f_1102_);
lean_dec_ref(v_toRing_1101_);
if (lean_obj_tag(v_charInst_x3f_1102_) == 0)
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1103_ = 0;
v___x_1104_ = lean_box(v___x_1103_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1104_);
v___x_1106_ = v___x_1099_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec_ref_known(v_charInst_x3f_1102_, 1);
v___x_1108_ = 1;
v___x_1109_ = lean_box(v___x_1108_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1109_);
v___x_1111_ = v___x_1099_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1096_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1096_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1134_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1163_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1163_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1163_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_toRing_1155_; lean_object* v_charInst_x3f_1156_; 
v_toRing_1155_ = lean_ctor_get(v_a_1151_, 0);
lean_inc_ref(v_toRing_1155_);
lean_dec(v_a_1151_);
v_charInst_x3f_1156_ = lean_ctor_get(v_toRing_1155_, 5);
lean_inc(v_charInst_x3f_1156_);
lean_dec_ref(v_toRing_1155_);
if (lean_obj_tag(v_charInst_x3f_1156_) == 1)
{
lean_object* v_val_1157_; lean_object* v___x_1159_; 
v_val_1157_ = lean_ctor_get(v_charInst_x3f_1156_, 0);
lean_inc(v_val_1157_);
lean_dec_ref_known(v_charInst_x3f_1156_, 1);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_val_1157_);
v___x_1159_ = v___x_1153_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_val_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_charInst_x3f_1156_);
lean_del_object(v___x_1153_);
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1162_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1161_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1150_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1150_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1213_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_fieldInst_x3f_1202_; 
v_fieldInst_x3f_1202_ = lean_ctor_get(v_a_1198_, 6);
lean_inc(v_fieldInst_x3f_1202_);
lean_dec(v_a_1198_);
if (lean_obj_tag(v_fieldInst_x3f_1202_) == 0)
{
uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = 0;
v___x_1204_ = lean_box(v___x_1203_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1204_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
lean_dec_ref_known(v_fieldInst_x3f_1202_, 1);
v___x_1208_ = 1;
v___x_1209_ = lean_box(v___x_1208_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1209_);
v___x_1211_ = v___x_1200_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1197_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1197_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1263_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1263_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1263_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_queue_1252_; 
v_queue_1252_ = lean_ctor_get(v_a_1248_, 11);
lean_inc(v_queue_1252_);
lean_dec(v_a_1248_);
if (lean_obj_tag(v_queue_1252_) == 0)
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_dec_ref_known(v_queue_1252_, 5);
v___x_1253_ = 0;
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1254_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = 1;
v___x_1259_ = lean_box(v___x_1258_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1259_);
v___x_1261_ = v___x_1250_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_a_1264_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1247_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1247_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1285_, lean_object* v_t_1286_){
_start:
{
if (lean_obj_tag(v_t_1286_) == 0)
{
lean_object* v_k_1287_; lean_object* v_v_1288_; lean_object* v_l_1289_; lean_object* v_r_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1944_; 
v_k_1287_ = lean_ctor_get(v_t_1286_, 1);
v_v_1288_ = lean_ctor_get(v_t_1286_, 2);
v_l_1289_ = lean_ctor_get(v_t_1286_, 3);
v_r_1290_ = lean_ctor_get(v_t_1286_, 4);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_t_1286_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v_t_1286_, 0);
lean_dec(v_unused_1945_);
v___x_1292_ = v_t_1286_;
v_isShared_1293_ = v_isSharedCheck_1944_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_r_1290_);
lean_inc(v_l_1289_);
lean_inc(v_v_1288_);
lean_inc(v_k_1287_);
lean_dec(v_t_1286_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1944_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1285_, v_k_1287_);
switch(v___x_1294_)
{
case 0:
{
lean_object* v_impl_1295_; lean_object* v___x_1296_; 
v_impl_1295_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1285_, v_l_1289_);
v___x_1296_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1295_) == 0)
{
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_size_1297_; lean_object* v_size_1298_; lean_object* v_k_1299_; lean_object* v_v_1300_; lean_object* v_l_1301_; lean_object* v_r_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_size_1297_ = lean_ctor_get(v_impl_1295_, 0);
lean_inc(v_size_1297_);
v_size_1298_ = lean_ctor_get(v_r_1290_, 0);
v_k_1299_ = lean_ctor_get(v_r_1290_, 1);
v_v_1300_ = lean_ctor_get(v_r_1290_, 2);
v_l_1301_ = lean_ctor_get(v_r_1290_, 3);
lean_inc(v_l_1301_);
v_r_1302_ = lean_ctor_get(v_r_1290_, 4);
v___x_1303_ = lean_unsigned_to_nat(3u);
v___x_1304_ = lean_nat_mul(v___x_1303_, v_size_1297_);
v___x_1305_ = lean_nat_dec_lt(v___x_1304_, v_size_1298_);
lean_dec(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
lean_dec(v_l_1301_);
v___x_1306_ = lean_nat_add(v___x_1296_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1307_ = lean_nat_add(v___x_1306_, v_size_1298_);
lean_dec(v___x_1306_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 3, v_impl_1295_);
lean_ctor_set(v___x_1292_, 0, v___x_1307_);
v___x_1309_ = v___x_1292_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_impl_1295_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_r_1290_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1374_; 
lean_inc(v_r_1302_);
lean_inc(v_v_1300_);
lean_inc(v_k_1299_);
lean_inc(v_size_1298_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; 
v_unused_1375_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1290_, 2);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1290_, 1);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1379_);
v___x_1312_ = v_r_1290_;
v_isShared_1313_ = v_isSharedCheck_1374_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v_r_1290_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1374_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_size_1314_; lean_object* v_k_1315_; lean_object* v_v_1316_; lean_object* v_l_1317_; lean_object* v_r_1318_; lean_object* v_size_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_size_1314_ = lean_ctor_get(v_l_1301_, 0);
v_k_1315_ = lean_ctor_get(v_l_1301_, 1);
v_v_1316_ = lean_ctor_get(v_l_1301_, 2);
v_l_1317_ = lean_ctor_get(v_l_1301_, 3);
v_r_1318_ = lean_ctor_get(v_l_1301_, 4);
v_size_1319_ = lean_ctor_get(v_r_1302_, 0);
v___x_1320_ = lean_unsigned_to_nat(2u);
v___x_1321_ = lean_nat_mul(v___x_1320_, v_size_1319_);
v___x_1322_ = lean_nat_dec_lt(v_size_1314_, v___x_1321_);
lean_dec(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_r_1318_);
lean_inc(v_l_1317_);
lean_inc(v_v_1316_);
lean_inc(v_k_1315_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_l_1301_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1351_ = lean_ctor_get(v_l_1301_, 4);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_l_1301_, 3);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1301_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1301_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1301_, 0);
lean_dec(v_unused_1355_);
v___x_1324_ = v_l_1301_;
v_isShared_1325_ = v_isSharedCheck_1350_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_l_1301_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1350_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1340_; 
v___x_1326_ = lean_nat_add(v___x_1296_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1327_ = lean_nat_add(v___x_1326_, v_size_1298_);
lean_dec(v_size_1298_);
if (lean_obj_tag(v_l_1317_) == 0)
{
lean_object* v_size_1348_; 
v_size_1348_ = lean_ctor_get(v_l_1317_, 0);
lean_inc(v_size_1348_);
v___y_1340_ = v_size_1348_;
goto v___jp_1339_;
}
else
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_unsigned_to_nat(0u);
v___y_1340_ = v___x_1349_;
goto v___jp_1339_;
}
v___jp_1328_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = lean_nat_add(v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec(v___y_1330_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 4, v_r_1302_);
lean_ctor_set(v___x_1324_, 3, v_r_1318_);
lean_ctor_set(v___x_1324_, 2, v_v_1300_);
lean_ctor_set(v___x_1324_, 1, v_k_1299_);
lean_ctor_set(v___x_1324_, 0, v___x_1332_);
v___x_1334_ = v___x_1324_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1299_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1300_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_r_1318_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_r_1302_);
v___x_1334_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 4, v___x_1334_);
lean_ctor_set(v___x_1312_, 3, v___y_1329_);
lean_ctor_set(v___x_1312_, 2, v_v_1316_);
lean_ctor_set(v___x_1312_, 1, v_k_1315_);
lean_ctor_set(v___x_1312_, 0, v___x_1327_);
v___x_1336_ = v___x_1312_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1315_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1316_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v___y_1329_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_nat_add(v___x_1326_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec(v___x_1326_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_l_1317_);
lean_ctor_set(v___x_1292_, 3, v_impl_1295_);
lean_ctor_set(v___x_1292_, 0, v___x_1341_);
v___x_1343_ = v___x_1292_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_impl_1295_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_l_1317_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_nat_add(v___x_1296_, v_size_1319_);
if (lean_obj_tag(v_r_1318_) == 0)
{
lean_object* v_size_1345_; 
v_size_1345_ = lean_ctor_get(v_r_1318_, 0);
lean_inc(v_size_1345_);
v___y_1329_ = v___x_1343_;
v___y_1330_ = v___x_1344_;
v___y_1331_ = v_size_1345_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___y_1329_ = v___x_1343_;
v___y_1330_ = v___x_1344_;
v___y_1331_ = v___x_1346_;
goto v___jp_1328_;
}
}
}
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_del_object(v___x_1292_);
v___x_1356_ = lean_nat_add(v___x_1296_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1357_ = lean_nat_add(v___x_1356_, v_size_1298_);
lean_dec(v_size_1298_);
v___x_1358_ = lean_nat_add(v___x_1356_, v_size_1314_);
lean_dec(v___x_1356_);
lean_inc_ref(v_impl_1295_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 4, v_l_1301_);
lean_ctor_set(v___x_1312_, 3, v_impl_1295_);
lean_ctor_set(v___x_1312_, 2, v_v_1288_);
lean_ctor_set(v___x_1312_, 1, v_k_1287_);
lean_ctor_set(v___x_1312_, 0, v___x_1358_);
v___x_1360_ = v___x_1312_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_impl_1295_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_l_1301_);
v___x_1360_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v_impl_1295_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1368_ = lean_ctor_get(v_impl_1295_, 4);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_impl_1295_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_impl_1295_, 2);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_impl_1295_, 1);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_impl_1295_, 0);
lean_dec(v_unused_1372_);
v___x_1362_ = v_impl_1295_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_impl_1295_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1302_);
lean_ctor_set(v___x_1362_, 3, v___x_1360_);
lean_ctor_set(v___x_1362_, 2, v_v_1300_);
lean_ctor_set(v___x_1362_, 1, v_k_1299_);
lean_ctor_set(v___x_1362_, 0, v___x_1357_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1299_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1300_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1302_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v_size_1380_ = lean_ctor_get(v_impl_1295_, 0);
lean_inc(v_size_1380_);
v___x_1381_ = lean_nat_add(v___x_1296_, v_size_1380_);
lean_dec(v_size_1380_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 3, v_impl_1295_);
lean_ctor_set(v___x_1292_, 0, v___x_1381_);
v___x_1383_ = v___x_1292_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_impl_1295_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_r_1290_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_l_1385_; 
v_l_1385_ = lean_ctor_get(v_r_1290_, 3);
lean_inc(v_l_1385_);
if (lean_obj_tag(v_l_1385_) == 0)
{
lean_object* v_r_1386_; 
v_r_1386_ = lean_ctor_get(v_r_1290_, 4);
lean_inc(v_r_1386_);
if (lean_obj_tag(v_r_1386_) == 0)
{
lean_object* v_size_1387_; lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1402_; 
v_size_1387_ = lean_ctor_get(v_r_1290_, 0);
v_k_1388_ = lean_ctor_get(v_r_1290_, 1);
v_v_1389_ = lean_ctor_get(v_r_1290_, 2);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; 
v_unused_1403_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1404_);
v___x_1391_ = v_r_1290_;
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_v_1389_);
lean_inc(v_k_1388_);
lean_inc(v_size_1387_);
lean_dec(v_r_1290_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_size_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v_size_1393_ = lean_ctor_get(v_l_1385_, 0);
v___x_1394_ = lean_nat_add(v___x_1296_, v_size_1387_);
lean_dec(v_size_1387_);
v___x_1395_ = lean_nat_add(v___x_1296_, v_size_1393_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v_l_1385_);
lean_ctor_set(v___x_1391_, 3, v_impl_1295_);
lean_ctor_set(v___x_1391_, 2, v_v_1288_);
lean_ctor_set(v___x_1391_, 1, v_k_1287_);
lean_ctor_set(v___x_1391_, 0, v___x_1395_);
v___x_1397_ = v___x_1391_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_impl_1295_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_l_1385_);
v___x_1397_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1386_);
lean_ctor_set(v___x_1292_, 3, v___x_1397_);
lean_ctor_set(v___x_1292_, 2, v_v_1389_);
lean_ctor_set(v___x_1292_, 1, v_k_1388_);
lean_ctor_set(v___x_1292_, 0, v___x_1394_);
v___x_1399_ = v___x_1292_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_r_1386_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1429_; 
v_k_1405_ = lean_ctor_get(v_r_1290_, 1);
v_v_1406_ = lean_ctor_get(v_r_1290_, 2);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1430_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1432_);
v___x_1408_ = v_r_1290_;
v_isShared_1409_ = v_isSharedCheck_1429_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_v_1406_);
lean_inc(v_k_1405_);
lean_dec(v_r_1290_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1429_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_k_1410_; lean_object* v_v_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1425_; 
v_k_1410_ = lean_ctor_get(v_l_1385_, 1);
v_v_1411_ = lean_ctor_get(v_l_1385_, 2);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_l_1385_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1426_ = lean_ctor_get(v_l_1385_, 4);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_l_1385_, 3);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_l_1385_, 0);
lean_dec(v_unused_1428_);
v___x_1413_ = v_l_1385_;
v_isShared_1414_ = v_isSharedCheck_1425_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_v_1411_);
lean_inc(v_k_1410_);
lean_dec(v_l_1385_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1425_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_unsigned_to_nat(3u);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 4, v_r_1386_);
lean_ctor_set(v___x_1413_, 3, v_r_1386_);
lean_ctor_set(v___x_1413_, 2, v_v_1288_);
lean_ctor_set(v___x_1413_, 1, v_k_1287_);
lean_ctor_set(v___x_1413_, 0, v___x_1296_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_r_1386_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_r_1386_);
v___x_1417_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 3, v_r_1386_);
lean_ctor_set(v___x_1408_, 0, v___x_1296_);
v___x_1419_ = v___x_1408_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_r_1386_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1386_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1421_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1419_);
lean_ctor_set(v___x_1292_, 3, v___x_1417_);
lean_ctor_set(v___x_1292_, 2, v_v_1411_);
lean_ctor_set(v___x_1292_, 1, v_k_1410_);
lean_ctor_set(v___x_1292_, 0, v___x_1415_);
v___x_1421_ = v___x_1292_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1433_; 
v_r_1433_ = lean_ctor_get(v_r_1290_, 4);
lean_inc(v_r_1433_);
if (lean_obj_tag(v_r_1433_) == 0)
{
lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1446_; 
v_k_1434_ = lean_ctor_get(v_r_1290_, 1);
v_v_1435_ = lean_ctor_get(v_r_1290_, 2);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1447_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1449_);
v___x_1437_ = v_r_1290_;
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_v_1435_);
lean_inc(v_k_1434_);
lean_dec(v_r_1290_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(3u);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v_l_1385_);
lean_ctor_set(v___x_1437_, 2, v_v_1288_);
lean_ctor_set(v___x_1437_, 1, v_k_1287_);
lean_ctor_set(v___x_1437_, 0, v___x_1296_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_l_1385_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_l_1385_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1433_);
lean_ctor_set(v___x_1292_, 3, v___x_1441_);
lean_ctor_set(v___x_1292_, 2, v_v_1435_);
lean_ctor_set(v___x_1292_, 1, v_k_1434_);
lean_ctor_set(v___x_1292_, 0, v___x_1439_);
v___x_1443_ = v___x_1292_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_r_1433_);
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
else
{
lean_object* v_size_1450_; lean_object* v_k_1451_; lean_object* v_v_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1463_; 
v_size_1450_ = lean_ctor_get(v_r_1290_, 0);
v_k_1451_ = lean_ctor_get(v_r_1290_, 1);
v_v_1452_ = lean_ctor_get(v_r_1290_, 2);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; 
v_unused_1464_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1465_);
v___x_1454_ = v_r_1290_;
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_v_1452_);
lean_inc(v_k_1451_);
lean_inc(v_size_1450_);
lean_dec(v_r_1290_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 3, v_r_1433_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_size_1450_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1451_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1452_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_r_1433_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_r_1433_);
v___x_1457_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_unsigned_to_nat(2u);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1457_);
lean_ctor_set(v___x_1292_, 3, v_r_1433_);
lean_ctor_set(v___x_1292_, 0, v___x_1458_);
v___x_1460_ = v___x_1292_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_r_1433_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v___x_1457_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
else
{
lean_object* v___x_1467_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 3, v_r_1290_);
lean_ctor_set(v___x_1292_, 0, v___x_1296_);
v___x_1467_ = v___x_1292_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_r_1290_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_r_1290_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1292_);
lean_dec(v_v_1288_);
lean_dec(v_k_1287_);
if (lean_obj_tag(v_l_1289_) == 0)
{
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_size_1469_; lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v_l_1472_; lean_object* v_r_1473_; lean_object* v_size_1474_; lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v_l_1477_; lean_object* v_r_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_size_1469_ = lean_ctor_get(v_l_1289_, 0);
v_k_1470_ = lean_ctor_get(v_l_1289_, 1);
v_v_1471_ = lean_ctor_get(v_l_1289_, 2);
v_l_1472_ = lean_ctor_get(v_l_1289_, 3);
v_r_1473_ = lean_ctor_get(v_l_1289_, 4);
lean_inc(v_r_1473_);
v_size_1474_ = lean_ctor_get(v_r_1290_, 0);
v_k_1475_ = lean_ctor_get(v_r_1290_, 1);
v_v_1476_ = lean_ctor_get(v_r_1290_, 2);
v_l_1477_ = lean_ctor_get(v_r_1290_, 3);
lean_inc(v_l_1477_);
v_r_1478_ = lean_ctor_get(v_r_1290_, 4);
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_dec_lt(v_size_1469_, v_size_1474_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1616_; 
lean_inc(v_l_1472_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; 
v_unused_1617_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_l_1289_, 2);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_l_1289_, 1);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1621_);
v___x_1482_ = v_l_1289_;
v_isShared_1483_ = v_isSharedCheck_1616_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v_l_1289_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1616_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v_tree_1485_; 
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1470_, v_v_1471_, v_l_1472_, v_r_1473_);
v_tree_1485_ = lean_ctor_get(v___x_1484_, 2);
lean_inc(v_tree_1485_);
if (lean_obj_tag(v_tree_1485_) == 0)
{
lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_size_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_k_1486_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_k_1486_);
v_v_1487_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_v_1487_);
lean_dec_ref(v___x_1484_);
v_size_1488_ = lean_ctor_get(v_tree_1485_, 0);
v___x_1489_ = lean_unsigned_to_nat(3u);
v___x_1490_ = lean_nat_mul(v___x_1489_, v_size_1488_);
v___x_1491_ = lean_nat_dec_lt(v___x_1490_, v_size_1474_);
lean_dec(v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v_l_1477_);
v___x_1492_ = lean_nat_add(v___x_1479_, v_size_1488_);
v___x_1493_ = lean_nat_add(v___x_1492_, v_size_1474_);
lean_dec(v___x_1492_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1290_);
lean_ctor_set(v___x_1482_, 3, v_tree_1485_);
lean_ctor_set(v___x_1482_, 2, v_v_1487_);
lean_ctor_set(v___x_1482_, 1, v_k_1486_);
lean_ctor_set(v___x_1482_, 0, v___x_1493_);
v___x_1495_ = v___x_1482_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1486_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1487_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_tree_1485_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v_r_1290_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
else
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1551_; 
lean_inc(v_r_1478_);
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
lean_inc(v_size_1474_);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; lean_object* v_unused_1554_; lean_object* v_unused_1555_; lean_object* v_unused_1556_; 
v_unused_1552_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_r_1290_, 2);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_r_1290_, 1);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1556_);
v___x_1498_ = v_r_1290_;
v_isShared_1499_ = v_isSharedCheck_1551_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_r_1290_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1551_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_size_1500_; lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_l_1503_; lean_object* v_r_1504_; lean_object* v_size_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_size_1500_ = lean_ctor_get(v_l_1477_, 0);
v_k_1501_ = lean_ctor_get(v_l_1477_, 1);
v_v_1502_ = lean_ctor_get(v_l_1477_, 2);
v_l_1503_ = lean_ctor_get(v_l_1477_, 3);
v_r_1504_ = lean_ctor_get(v_l_1477_, 4);
v_size_1505_ = lean_ctor_get(v_r_1478_, 0);
v___x_1506_ = lean_unsigned_to_nat(2u);
v___x_1507_ = lean_nat_mul(v___x_1506_, v_size_1505_);
v___x_1508_ = lean_nat_dec_lt(v_size_1500_, v___x_1507_);
lean_dec(v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1536_; 
lean_inc(v_r_1504_);
lean_inc(v_l_1503_);
lean_inc(v_v_1502_);
lean_inc(v_k_1501_);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_l_1477_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1537_ = lean_ctor_get(v_l_1477_, 4);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_l_1477_, 3);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_l_1477_, 2);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1477_, 1);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_l_1477_, 0);
lean_dec(v_unused_1541_);
v___x_1510_ = v_l_1477_;
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v_l_1477_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1536_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1526_; 
v___x_1512_ = lean_nat_add(v___x_1479_, v_size_1488_);
v___x_1513_ = lean_nat_add(v___x_1512_, v_size_1474_);
lean_dec(v_size_1474_);
if (lean_obj_tag(v_l_1503_) == 0)
{
lean_object* v_size_1534_; 
v_size_1534_ = lean_ctor_get(v_l_1503_, 0);
lean_inc(v_size_1534_);
v___y_1526_ = v_size_1534_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(0u);
v___y_1526_ = v___x_1535_;
goto v___jp_1525_;
}
v___jp_1514_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_nat_add(v___y_1515_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec(v___y_1515_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 4, v_r_1478_);
lean_ctor_set(v___x_1510_, 3, v_r_1504_);
lean_ctor_set(v___x_1510_, 2, v_v_1476_);
lean_ctor_set(v___x_1510_, 1, v_k_1475_);
lean_ctor_set(v___x_1510_, 0, v___x_1518_);
v___x_1520_ = v___x_1510_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_r_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1478_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v___x_1520_);
lean_ctor_set(v___x_1498_, 3, v___y_1516_);
lean_ctor_set(v___x_1498_, 2, v_v_1502_);
lean_ctor_set(v___x_1498_, 1, v_k_1501_);
lean_ctor_set(v___x_1498_, 0, v___x_1513_);
v___x_1522_ = v___x_1498_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1501_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1502_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v___y_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
v___jp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = lean_nat_add(v___x_1512_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec(v___x_1512_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_l_1503_);
lean_ctor_set(v___x_1482_, 3, v_tree_1485_);
lean_ctor_set(v___x_1482_, 2, v_v_1487_);
lean_ctor_set(v___x_1482_, 1, v_k_1486_);
lean_ctor_set(v___x_1482_, 0, v___x_1527_);
v___x_1529_ = v___x_1482_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1486_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1487_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_tree_1485_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_l_1503_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_nat_add(v___x_1479_, v_size_1505_);
if (lean_obj_tag(v_r_1504_) == 0)
{
lean_object* v_size_1531_; 
v_size_1531_ = lean_ctor_get(v_r_1504_, 0);
lean_inc(v_size_1531_);
v___y_1515_ = v___x_1530_;
v___y_1516_ = v___x_1529_;
v___y_1517_ = v_size_1531_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___y_1515_ = v___x_1530_;
v___y_1516_ = v___x_1529_;
v___y_1517_ = v___x_1532_;
goto v___jp_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1542_ = lean_nat_add(v___x_1479_, v_size_1488_);
v___x_1543_ = lean_nat_add(v___x_1542_, v_size_1474_);
lean_dec(v_size_1474_);
v___x_1544_ = lean_nat_add(v___x_1542_, v_size_1500_);
lean_dec(v___x_1542_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 4, v_l_1477_);
lean_ctor_set(v___x_1498_, 3, v_tree_1485_);
lean_ctor_set(v___x_1498_, 2, v_v_1487_);
lean_ctor_set(v___x_1498_, 1, v_k_1486_);
lean_ctor_set(v___x_1498_, 0, v___x_1544_);
v___x_1546_ = v___x_1498_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1486_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1487_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_tree_1485_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_l_1477_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1546_);
lean_ctor_set(v___x_1482_, 2, v_v_1476_);
lean_ctor_set(v___x_1482_, 1, v_k_1475_);
lean_ctor_set(v___x_1482_, 0, v___x_1543_);
v___x_1548_ = v___x_1482_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1478_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
else
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1610_; 
lean_inc(v_r_1478_);
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
lean_inc(v_size_1474_);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; 
v_unused_1611_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1290_, 2);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1290_, 1);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1615_);
v___x_1558_ = v_r_1290_;
v_isShared_1559_ = v_isSharedCheck_1610_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v_r_1290_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1610_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
if (lean_obj_tag(v_l_1477_) == 0)
{
if (lean_obj_tag(v_r_1478_) == 0)
{
lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v_size_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v_k_1560_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_k_1560_);
v_v_1561_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_v_1561_);
lean_dec_ref(v___x_1484_);
v_size_1562_ = lean_ctor_get(v_l_1477_, 0);
v___x_1563_ = lean_nat_add(v___x_1479_, v_size_1474_);
lean_dec(v_size_1474_);
v___x_1564_ = lean_nat_add(v___x_1479_, v_size_1562_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 4, v_l_1477_);
lean_ctor_set(v___x_1558_, 3, v_tree_1485_);
lean_ctor_set(v___x_1558_, 2, v_v_1561_);
lean_ctor_set(v___x_1558_, 1, v_k_1560_);
lean_ctor_set(v___x_1558_, 0, v___x_1564_);
v___x_1566_ = v___x_1558_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1561_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_tree_1485_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_l_1477_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1566_);
lean_ctor_set(v___x_1482_, 2, v_v_1476_);
lean_ctor_set(v___x_1482_, 1, v_k_1475_);
lean_ctor_set(v___x_1482_, 0, v___x_1563_);
v___x_1568_ = v___x_1482_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_r_1478_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v_k_1573_; lean_object* v_v_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_size_1474_);
v_k_1571_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_k_1571_);
v_v_1572_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_v_1572_);
lean_dec_ref(v___x_1484_);
v_k_1573_ = lean_ctor_get(v_l_1477_, 1);
v_v_1574_ = lean_ctor_get(v_l_1477_, 2);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_l_1477_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; 
v_unused_1589_ = lean_ctor_get(v_l_1477_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1477_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1477_, 0);
lean_dec(v_unused_1591_);
v___x_1576_ = v_l_1477_;
v_isShared_1577_ = v_isSharedCheck_1588_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_v_1574_);
lean_inc(v_k_1573_);
lean_dec(v_l_1477_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1588_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_unsigned_to_nat(3u);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 4, v_r_1478_);
lean_ctor_set(v___x_1576_, 3, v_r_1478_);
lean_ctor_set(v___x_1576_, 2, v_v_1572_);
lean_ctor_set(v___x_1576_, 1, v_k_1571_);
lean_ctor_set(v___x_1576_, 0, v___x_1479_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_r_1478_);
v___x_1580_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 3, v_r_1478_);
lean_ctor_set(v___x_1558_, 0, v___x_1479_);
v___x_1582_ = v___x_1558_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_r_1478_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_1582_);
lean_ctor_set(v___x_1482_, 3, v___x_1580_);
lean_ctor_set(v___x_1482_, 2, v_v_1574_);
lean_ctor_set(v___x_1482_, 1, v_k_1573_);
lean_ctor_set(v___x_1482_, 0, v___x_1578_);
v___x_1584_ = v___x_1482_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1573_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1574_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1478_) == 0)
{
lean_object* v_k_1592_; lean_object* v_v_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_size_1474_);
v_k_1592_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_k_1592_);
v_v_1593_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_v_1593_);
lean_dec_ref(v___x_1484_);
v___x_1594_ = lean_unsigned_to_nat(3u);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 4, v_l_1477_);
lean_ctor_set(v___x_1558_, 2, v_v_1593_);
lean_ctor_set(v___x_1558_, 1, v_k_1592_);
lean_ctor_set(v___x_1558_, 0, v___x_1479_);
v___x_1596_ = v___x_1558_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1477_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_l_1477_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_r_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1596_);
lean_ctor_set(v___x_1482_, 2, v_v_1476_);
lean_ctor_set(v___x_1482_, 1, v_k_1475_);
lean_ctor_set(v___x_1482_, 0, v___x_1594_);
v___x_1598_ = v___x_1482_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_r_1478_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_k_1601_; lean_object* v_v_1602_; lean_object* v___x_1604_; 
v_k_1601_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_k_1601_);
v_v_1602_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_v_1602_);
lean_dec_ref(v___x_1484_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 3, v_r_1478_);
v___x_1604_ = v___x_1558_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_size_1474_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1475_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1476_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_r_1478_);
v___x_1604_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(2u);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_1604_);
lean_ctor_set(v___x_1482_, 3, v_r_1478_);
lean_ctor_set(v___x_1482_, 2, v_v_1602_);
lean_ctor_set(v___x_1482_, 1, v_k_1601_);
lean_ctor_set(v___x_1482_, 0, v___x_1605_);
v___x_1607_ = v___x_1482_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_r_1478_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1604_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
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
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1774_; 
lean_inc(v_r_1478_);
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; 
v_unused_1775_ = lean_ctor_get(v_r_1290_, 4);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_r_1290_, 3);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_r_1290_, 2);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_r_1290_, 1);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_r_1290_, 0);
lean_dec(v_unused_1779_);
v___x_1623_ = v_r_1290_;
v_isShared_1624_ = v_isSharedCheck_1774_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_r_1290_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1774_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v_tree_1626_; 
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1475_, v_v_1476_, v_l_1477_, v_r_1478_);
v_tree_1626_ = lean_ctor_get(v___x_1625_, 2);
lean_inc(v_tree_1626_);
if (lean_obj_tag(v_tree_1626_) == 0)
{
lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v_size_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v_k_1627_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_k_1627_);
v_v_1628_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_v_1628_);
lean_dec_ref(v___x_1625_);
v_size_1629_ = lean_ctor_get(v_tree_1626_, 0);
v___x_1630_ = lean_unsigned_to_nat(3u);
v___x_1631_ = lean_nat_mul(v___x_1630_, v_size_1629_);
v___x_1632_ = lean_nat_dec_lt(v___x_1631_, v_size_1469_);
lean_dec(v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_dec(v_r_1473_);
v___x_1633_ = lean_nat_add(v___x_1479_, v_size_1469_);
v___x_1634_ = lean_nat_add(v___x_1633_, v_size_1629_);
lean_dec(v___x_1633_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_tree_1626_);
lean_ctor_set(v___x_1623_, 3, v_l_1289_);
lean_ctor_set(v___x_1623_, 2, v_v_1628_);
lean_ctor_set(v___x_1623_, 1, v_k_1627_);
lean_ctor_set(v___x_1623_, 0, v___x_1634_);
v___x_1636_ = v___x_1623_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_tree_1626_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
else
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_l_1472_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
lean_inc(v_size_1469_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1704_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1289_, 2);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_l_1289_, 1);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1708_);
v___x_1639_ = v_l_1289_;
v_isShared_1640_ = v_isSharedCheck_1703_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v_l_1289_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1703_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_size_1641_; lean_object* v_size_1642_; lean_object* v_k_1643_; lean_object* v_v_1644_; lean_object* v_l_1645_; lean_object* v_r_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_size_1641_ = lean_ctor_get(v_l_1472_, 0);
v_size_1642_ = lean_ctor_get(v_r_1473_, 0);
v_k_1643_ = lean_ctor_get(v_r_1473_, 1);
v_v_1644_ = lean_ctor_get(v_r_1473_, 2);
v_l_1645_ = lean_ctor_get(v_r_1473_, 3);
v_r_1646_ = lean_ctor_get(v_r_1473_, 4);
v___x_1647_ = lean_unsigned_to_nat(2u);
v___x_1648_ = lean_nat_mul(v___x_1647_, v_size_1641_);
v___x_1649_ = lean_nat_dec_lt(v_size_1642_, v___x_1648_);
lean_dec(v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1687_; 
lean_inc(v_r_1646_);
lean_inc(v_l_1645_);
lean_inc(v_v_1644_);
lean_inc(v_k_1643_);
lean_del_object(v___x_1639_);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_r_1473_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1688_ = lean_ctor_get(v_r_1473_, 4);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_r_1473_, 3);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_r_1473_, 2);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_r_1473_, 1);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_r_1473_, 0);
lean_dec(v_unused_1692_);
v___x_1651_ = v_r_1473_;
v_isShared_1652_ = v_isSharedCheck_1687_;
goto v_resetjp_1650_;
}
else
{
lean_dec(v_r_1473_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1687_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___x_1675_; lean_object* v___y_1677_; 
v___x_1653_ = lean_nat_add(v___x_1479_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1654_ = lean_nat_add(v___x_1653_, v_size_1629_);
lean_dec(v___x_1653_);
v___x_1675_ = lean_nat_add(v___x_1479_, v_size_1641_);
if (lean_obj_tag(v_l_1645_) == 0)
{
lean_object* v_size_1685_; 
v_size_1685_ = lean_ctor_get(v_l_1645_, 0);
lean_inc(v_size_1685_);
v___y_1677_ = v_size_1685_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_unsigned_to_nat(0u);
v___y_1677_ = v___x_1686_;
goto v___jp_1676_;
}
v___jp_1655_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_nat_add(v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec(v___y_1657_);
lean_inc_ref(v_tree_1626_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v_tree_1626_);
lean_ctor_set(v___x_1651_, 3, v_r_1646_);
lean_ctor_set(v___x_1651_, 2, v_v_1628_);
lean_ctor_set(v___x_1651_, 1, v_k_1627_);
lean_ctor_set(v___x_1651_, 0, v___x_1659_);
v___x_1661_ = v___x_1651_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_r_1646_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_tree_1626_);
v___x_1661_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_isSharedCheck_1668_ = !lean_is_exclusive(v_tree_1626_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; 
v_unused_1669_ = lean_ctor_get(v_tree_1626_, 4);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_tree_1626_, 3);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_tree_1626_, 2);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_tree_1626_, 1);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_tree_1626_, 0);
lean_dec(v_unused_1673_);
v___x_1663_ = v_tree_1626_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_dec(v_tree_1626_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 4, v___x_1661_);
lean_ctor_set(v___x_1663_, 3, v___y_1656_);
lean_ctor_set(v___x_1663_, 2, v_v_1644_);
lean_ctor_set(v___x_1663_, 1, v_k_1643_);
lean_ctor_set(v___x_1663_, 0, v___x_1654_);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1643_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1644_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v___y_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
v___jp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_nat_add(v___x_1675_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec(v___x_1675_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_l_1645_);
lean_ctor_set(v___x_1623_, 3, v_l_1472_);
lean_ctor_set(v___x_1623_, 2, v_v_1471_);
lean_ctor_set(v___x_1623_, 1, v_k_1470_);
lean_ctor_set(v___x_1623_, 0, v___x_1678_);
v___x_1680_ = v___x_1623_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_l_1645_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_nat_add(v___x_1479_, v_size_1629_);
if (lean_obj_tag(v_r_1646_) == 0)
{
lean_object* v_size_1682_; 
v_size_1682_ = lean_ctor_get(v_r_1646_, 0);
lean_inc(v_size_1682_);
v___y_1656_ = v___x_1680_;
v___y_1657_ = v___x_1681_;
v___y_1658_ = v_size_1682_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___y_1656_ = v___x_1680_;
v___y_1657_ = v___x_1681_;
v___y_1658_ = v___x_1683_;
goto v___jp_1655_;
}
}
}
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1693_ = lean_nat_add(v___x_1479_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1694_ = lean_nat_add(v___x_1693_, v_size_1629_);
lean_dec(v___x_1693_);
v___x_1695_ = lean_nat_add(v___x_1479_, v_size_1629_);
v___x_1696_ = lean_nat_add(v___x_1695_, v_size_1642_);
lean_dec(v___x_1695_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_tree_1626_);
lean_ctor_set(v___x_1623_, 3, v_r_1473_);
lean_ctor_set(v___x_1623_, 2, v_v_1628_);
lean_ctor_set(v___x_1623_, 1, v_k_1627_);
lean_ctor_set(v___x_1623_, 0, v___x_1696_);
v___x_1698_ = v___x_1623_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_tree_1626_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 4, v___x_1698_);
lean_ctor_set(v___x_1639_, 0, v___x_1694_);
v___x_1700_ = v___x_1639_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1472_) == 0)
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1732_; 
lean_inc_ref(v_l_1472_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
lean_inc(v_size_1469_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; lean_object* v_unused_1736_; lean_object* v_unused_1737_; 
v_unused_1733_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1289_, 2);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_l_1289_, 1);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1737_);
v___x_1710_ = v_l_1289_;
v_isShared_1711_ = v_isSharedCheck_1732_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v_l_1289_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1732_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v_k_1712_; lean_object* v_v_1713_; lean_object* v_size_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v_k_1712_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_k_1712_);
v_v_1713_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_v_1713_);
lean_dec_ref(v___x_1625_);
v_size_1714_ = lean_ctor_get(v_r_1473_, 0);
v___x_1715_ = lean_nat_add(v___x_1479_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1716_ = lean_nat_add(v___x_1479_, v_size_1714_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_tree_1626_);
lean_ctor_set(v___x_1623_, 3, v_r_1473_);
lean_ctor_set(v___x_1623_, 2, v_v_1713_);
lean_ctor_set(v___x_1623_, 1, v_k_1712_);
lean_ctor_set(v___x_1623_, 0, v___x_1716_);
v___x_1718_ = v___x_1623_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_tree_1626_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 4, v___x_1718_);
lean_ctor_set(v___x_1710_, 0, v___x_1715_);
v___x_1720_ = v___x_1710_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_k_1723_; lean_object* v_v_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec(v_size_1469_);
v_k_1723_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_k_1723_);
v_v_1724_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_v_1724_);
lean_dec_ref(v___x_1625_);
v___x_1725_ = lean_unsigned_to_nat(3u);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_r_1473_);
lean_ctor_set(v___x_1623_, 3, v_r_1473_);
lean_ctor_set(v___x_1623_, 2, v_v_1724_);
lean_ctor_set(v___x_1623_, 1, v_k_1723_);
lean_ctor_set(v___x_1623_, 0, v___x_1479_);
v___x_1727_ = v___x_1623_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_k_1723_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_v_1724_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v_r_1473_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 4, v___x_1727_);
lean_ctor_set(v___x_1710_, 0, v___x_1725_);
v___x_1729_ = v___x_1710_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1762_; 
lean_inc(v_l_1472_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; lean_object* v_unused_1767_; 
v_unused_1763_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_l_1289_, 2);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1289_, 1);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1767_);
v___x_1739_ = v_l_1289_;
v_isShared_1740_ = v_isSharedCheck_1762_;
goto v_resetjp_1738_;
}
else
{
lean_dec(v_l_1289_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1762_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_k_1741_; lean_object* v_v_1742_; lean_object* v_k_1743_; lean_object* v_v_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1758_; 
v_k_1741_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_k_1741_);
v_v_1742_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_v_1742_);
lean_dec_ref(v___x_1625_);
v_k_1743_ = lean_ctor_get(v_r_1473_, 1);
v_v_1744_ = lean_ctor_get(v_r_1473_, 2);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_r_1473_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; lean_object* v_unused_1760_; lean_object* v_unused_1761_; 
v_unused_1759_ = lean_ctor_get(v_r_1473_, 4);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_r_1473_, 3);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_r_1473_, 0);
lean_dec(v_unused_1761_);
v___x_1746_ = v_r_1473_;
v_isShared_1747_ = v_isSharedCheck_1758_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_v_1744_);
lean_inc(v_k_1743_);
lean_dec(v_r_1473_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1758_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_unsigned_to_nat(3u);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 4, v_l_1472_);
lean_ctor_set(v___x_1746_, 3, v_l_1472_);
lean_ctor_set(v___x_1746_, 2, v_v_1471_);
lean_ctor_set(v___x_1746_, 1, v_k_1470_);
lean_ctor_set(v___x_1746_, 0, v___x_1479_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_l_1472_);
v___x_1750_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_l_1472_);
lean_ctor_set(v___x_1623_, 3, v_l_1472_);
lean_ctor_set(v___x_1623_, 2, v_v_1742_);
lean_ctor_set(v___x_1623_, 1, v_k_1741_);
lean_ctor_set(v___x_1623_, 0, v___x_1479_);
v___x_1752_ = v___x_1623_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1741_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1742_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_l_1472_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 4, v___x_1752_);
lean_ctor_set(v___x_1739_, 3, v___x_1750_);
lean_ctor_set(v___x_1739_, 2, v_v_1744_);
lean_ctor_set(v___x_1739_, 1, v_k_1743_);
lean_ctor_set(v___x_1739_, 0, v___x_1748_);
v___x_1754_ = v___x_1739_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_k_1743_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_v_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
else
{
lean_object* v_k_1768_; lean_object* v_v_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v_k_1768_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_k_1768_);
v_v_1769_ = lean_ctor_get(v___x_1625_, 1);
lean_inc(v_v_1769_);
lean_dec_ref(v___x_1625_);
v___x_1770_ = lean_unsigned_to_nat(2u);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v_r_1473_);
lean_ctor_set(v___x_1623_, 3, v_l_1289_);
lean_ctor_set(v___x_1623_, 2, v_v_1769_);
lean_ctor_set(v___x_1623_, 1, v_k_1768_);
lean_ctor_set(v___x_1623_, 0, v___x_1770_);
v___x_1772_ = v___x_1623_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_k_1768_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_v_1769_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v_r_1473_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
}
else
{
return v_l_1289_;
}
}
else
{
return v_r_1290_;
}
}
default: 
{
lean_object* v_impl_1780_; lean_object* v___x_1781_; 
v_impl_1780_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1285_, v_r_1290_);
v___x_1781_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1780_) == 0)
{
if (lean_obj_tag(v_l_1289_) == 0)
{
lean_object* v_size_1782_; lean_object* v_size_1783_; lean_object* v_k_1784_; lean_object* v_v_1785_; lean_object* v_l_1786_; lean_object* v_r_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_size_1782_ = lean_ctor_get(v_impl_1780_, 0);
lean_inc(v_size_1782_);
v_size_1783_ = lean_ctor_get(v_l_1289_, 0);
v_k_1784_ = lean_ctor_get(v_l_1289_, 1);
v_v_1785_ = lean_ctor_get(v_l_1289_, 2);
v_l_1786_ = lean_ctor_get(v_l_1289_, 3);
v_r_1787_ = lean_ctor_get(v_l_1289_, 4);
lean_inc(v_r_1787_);
v___x_1788_ = lean_unsigned_to_nat(3u);
v___x_1789_ = lean_nat_mul(v___x_1788_, v_size_1782_);
v___x_1790_ = lean_nat_dec_lt(v___x_1789_, v_size_1783_);
lean_dec(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec(v_r_1787_);
v___x_1791_ = lean_nat_add(v___x_1781_, v_size_1783_);
v___x_1792_ = lean_nat_add(v___x_1791_, v_size_1782_);
lean_dec(v_size_1782_);
lean_dec(v___x_1791_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_impl_1780_);
lean_ctor_set(v___x_1292_, 0, v___x_1792_);
v___x_1794_ = v___x_1292_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_impl_1780_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
else
{
lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1861_; 
lean_inc(v_l_1786_);
lean_inc(v_v_1785_);
lean_inc(v_k_1784_);
lean_inc(v_size_1783_);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; 
v_unused_1862_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_l_1289_, 2);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_l_1289_, 1);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1866_);
v___x_1797_ = v_l_1289_;
v_isShared_1798_ = v_isSharedCheck_1861_;
goto v_resetjp_1796_;
}
else
{
lean_dec(v_l_1289_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1861_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_size_1799_; lean_object* v_size_1800_; lean_object* v_k_1801_; lean_object* v_v_1802_; lean_object* v_l_1803_; lean_object* v_r_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_size_1799_ = lean_ctor_get(v_l_1786_, 0);
v_size_1800_ = lean_ctor_get(v_r_1787_, 0);
v_k_1801_ = lean_ctor_get(v_r_1787_, 1);
v_v_1802_ = lean_ctor_get(v_r_1787_, 2);
v_l_1803_ = lean_ctor_get(v_r_1787_, 3);
v_r_1804_ = lean_ctor_get(v_r_1787_, 4);
v___x_1805_ = lean_unsigned_to_nat(2u);
v___x_1806_ = lean_nat_mul(v___x_1805_, v_size_1799_);
v___x_1807_ = lean_nat_dec_lt(v_size_1800_, v___x_1806_);
lean_dec(v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1836_; 
lean_inc(v_r_1804_);
lean_inc(v_l_1803_);
lean_inc(v_v_1802_);
lean_inc(v_k_1801_);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_r_1787_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; 
v_unused_1837_ = lean_ctor_get(v_r_1787_, 4);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_r_1787_, 3);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_r_1787_, 2);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1787_, 1);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_r_1787_, 0);
lean_dec(v_unused_1841_);
v___x_1809_ = v_r_1787_;
v_isShared_1810_ = v_isSharedCheck_1836_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_r_1787_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1836_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___x_1824_; lean_object* v___y_1826_; 
v___x_1811_ = lean_nat_add(v___x_1781_, v_size_1783_);
lean_dec(v_size_1783_);
v___x_1812_ = lean_nat_add(v___x_1811_, v_size_1782_);
lean_dec(v___x_1811_);
v___x_1824_ = lean_nat_add(v___x_1781_, v_size_1799_);
if (lean_obj_tag(v_l_1803_) == 0)
{
lean_object* v_size_1834_; 
v_size_1834_ = lean_ctor_get(v_l_1803_, 0);
lean_inc(v_size_1834_);
v___y_1826_ = v_size_1834_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___y_1826_ = v___x_1835_;
goto v___jp_1825_;
}
v___jp_1813_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_nat_add(v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec(v___y_1815_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 4, v_impl_1780_);
lean_ctor_set(v___x_1809_, 3, v_r_1804_);
lean_ctor_set(v___x_1809_, 2, v_v_1288_);
lean_ctor_set(v___x_1809_, 1, v_k_1287_);
lean_ctor_set(v___x_1809_, 0, v___x_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_r_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_impl_1780_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 4, v___x_1819_);
lean_ctor_set(v___x_1797_, 3, v___y_1814_);
lean_ctor_set(v___x_1797_, 2, v_v_1802_);
lean_ctor_set(v___x_1797_, 1, v_k_1801_);
lean_ctor_set(v___x_1797_, 0, v___x_1812_);
v___x_1821_ = v___x_1797_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1801_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1802_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v___y_1814_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
v___jp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = lean_nat_add(v___x_1824_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec(v___x_1824_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_l_1803_);
lean_ctor_set(v___x_1292_, 3, v_l_1786_);
lean_ctor_set(v___x_1292_, 2, v_v_1785_);
lean_ctor_set(v___x_1292_, 1, v_k_1784_);
lean_ctor_set(v___x_1292_, 0, v___x_1827_);
v___x_1829_ = v___x_1292_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_k_1784_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_v_1785_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_l_1786_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v_l_1803_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_nat_add(v___x_1781_, v_size_1782_);
lean_dec(v_size_1782_);
if (lean_obj_tag(v_r_1804_) == 0)
{
lean_object* v_size_1831_; 
v_size_1831_ = lean_ctor_get(v_r_1804_, 0);
lean_inc(v_size_1831_);
v___y_1814_ = v___x_1829_;
v___y_1815_ = v___x_1830_;
v___y_1816_ = v_size_1831_;
goto v___jp_1813_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_unsigned_to_nat(0u);
v___y_1814_ = v___x_1829_;
v___y_1815_ = v___x_1830_;
v___y_1816_ = v___x_1832_;
goto v___jp_1813_;
}
}
}
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_del_object(v___x_1292_);
v___x_1842_ = lean_nat_add(v___x_1781_, v_size_1783_);
lean_dec(v_size_1783_);
v___x_1843_ = lean_nat_add(v___x_1842_, v_size_1782_);
lean_dec(v___x_1842_);
v___x_1844_ = lean_nat_add(v___x_1781_, v_size_1782_);
lean_dec(v_size_1782_);
v___x_1845_ = lean_nat_add(v___x_1844_, v_size_1800_);
lean_dec(v___x_1844_);
lean_inc_ref(v_impl_1780_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 4, v_impl_1780_);
lean_ctor_set(v___x_1797_, 3, v_r_1787_);
lean_ctor_set(v___x_1797_, 2, v_v_1288_);
lean_ctor_set(v___x_1797_, 1, v_k_1287_);
lean_ctor_set(v___x_1797_, 0, v___x_1845_);
v___x_1847_ = v___x_1797_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_r_1787_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_impl_1780_);
v___x_1847_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_isSharedCheck_1854_ = !lean_is_exclusive(v_impl_1780_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1855_ = lean_ctor_get(v_impl_1780_, 4);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_impl_1780_, 3);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_impl_1780_, 2);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_impl_1780_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_impl_1780_, 0);
lean_dec(v_unused_1859_);
v___x_1849_ = v_impl_1780_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v_impl_1780_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 4, v___x_1847_);
lean_ctor_set(v___x_1849_, 3, v_l_1786_);
lean_ctor_set(v___x_1849_, 2, v_v_1785_);
lean_ctor_set(v___x_1849_, 1, v_k_1784_);
lean_ctor_set(v___x_1849_, 0, v___x_1843_);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_k_1784_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_v_1785_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_l_1786_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v___x_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v_size_1867_ = lean_ctor_get(v_impl_1780_, 0);
lean_inc(v_size_1867_);
v___x_1868_ = lean_nat_add(v___x_1781_, v_size_1867_);
lean_dec(v_size_1867_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_impl_1780_);
lean_ctor_set(v___x_1292_, 0, v___x_1868_);
v___x_1870_ = v___x_1292_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_impl_1780_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
if (lean_obj_tag(v_l_1289_) == 0)
{
lean_object* v_l_1872_; 
v_l_1872_ = lean_ctor_get(v_l_1289_, 3);
if (lean_obj_tag(v_l_1872_) == 0)
{
lean_object* v_r_1873_; 
lean_inc_ref(v_l_1872_);
v_r_1873_ = lean_ctor_get(v_l_1289_, 4);
lean_inc(v_r_1873_);
if (lean_obj_tag(v_r_1873_) == 0)
{
lean_object* v_size_1874_; lean_object* v_k_1875_; lean_object* v_v_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1889_; 
v_size_1874_ = lean_ctor_get(v_l_1289_, 0);
v_k_1875_ = lean_ctor_get(v_l_1289_, 1);
v_v_1876_ = lean_ctor_get(v_l_1289_, 2);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; lean_object* v_unused_1891_; 
v_unused_1890_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1891_);
v___x_1878_ = v_l_1289_;
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_v_1876_);
lean_inc(v_k_1875_);
lean_inc(v_size_1874_);
lean_dec(v_l_1289_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_size_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v_size_1880_ = lean_ctor_get(v_r_1873_, 0);
v___x_1881_ = lean_nat_add(v___x_1781_, v_size_1874_);
lean_dec(v_size_1874_);
v___x_1882_ = lean_nat_add(v___x_1781_, v_size_1880_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 4, v_impl_1780_);
lean_ctor_set(v___x_1878_, 3, v_r_1873_);
lean_ctor_set(v___x_1878_, 2, v_v_1288_);
lean_ctor_set(v___x_1878_, 1, v_k_1287_);
lean_ctor_set(v___x_1878_, 0, v___x_1882_);
v___x_1884_ = v___x_1878_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_r_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_impl_1780_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1884_);
lean_ctor_set(v___x_1292_, 3, v_l_1872_);
lean_ctor_set(v___x_1292_, 2, v_v_1876_);
lean_ctor_set(v___x_1292_, 1, v_k_1875_);
lean_ctor_set(v___x_1292_, 0, v___x_1881_);
v___x_1886_ = v___x_1292_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_k_1875_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_v_1876_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_l_1872_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_k_1892_; lean_object* v_v_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1904_; 
v_k_1892_ = lean_ctor_get(v_l_1289_, 1);
v_v_1893_ = lean_ctor_get(v_l_1289_, 2);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; 
v_unused_1905_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1907_);
v___x_1895_ = v_l_1289_;
v_isShared_1896_ = v_isSharedCheck_1904_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_v_1893_);
lean_inc(v_k_1892_);
lean_dec(v_l_1289_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1904_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(3u);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 3, v_r_1873_);
lean_ctor_set(v___x_1895_, 2, v_v_1288_);
lean_ctor_set(v___x_1895_, 1, v_k_1287_);
lean_ctor_set(v___x_1895_, 0, v___x_1781_);
v___x_1899_ = v___x_1895_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_r_1873_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_r_1873_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1899_);
lean_ctor_set(v___x_1292_, 3, v_l_1872_);
lean_ctor_set(v___x_1292_, 2, v_v_1893_);
lean_ctor_set(v___x_1292_, 1, v_k_1892_);
lean_ctor_set(v___x_1292_, 0, v___x_1897_);
v___x_1901_ = v___x_1292_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_k_1892_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_v_1893_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_l_1872_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
else
{
lean_object* v_r_1908_; 
v_r_1908_ = lean_ctor_get(v_l_1289_, 4);
lean_inc(v_r_1908_);
if (lean_obj_tag(v_r_1908_) == 0)
{
lean_object* v_k_1909_; lean_object* v_v_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1933_; 
lean_inc(v_l_1872_);
v_k_1909_ = lean_ctor_get(v_l_1289_, 1);
v_v_1910_ = lean_ctor_get(v_l_1289_, 2);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_l_1289_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1934_ = lean_ctor_get(v_l_1289_, 4);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_l_1289_, 3);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_l_1289_, 0);
lean_dec(v_unused_1936_);
v___x_1912_ = v_l_1289_;
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_v_1910_);
lean_inc(v_k_1909_);
lean_dec(v_l_1289_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_k_1914_; lean_object* v_v_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1929_; 
v_k_1914_ = lean_ctor_get(v_r_1908_, 1);
v_v_1915_ = lean_ctor_get(v_r_1908_, 2);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_r_1908_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; lean_object* v_unused_1931_; lean_object* v_unused_1932_; 
v_unused_1930_ = lean_ctor_get(v_r_1908_, 4);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_r_1908_, 3);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_r_1908_, 0);
lean_dec(v_unused_1932_);
v___x_1917_ = v_r_1908_;
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_v_1915_);
lean_inc(v_k_1914_);
lean_dec(v_r_1908_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(3u);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v_l_1872_);
lean_ctor_set(v___x_1917_, 3, v_l_1872_);
lean_ctor_set(v___x_1917_, 2, v_v_1910_);
lean_ctor_set(v___x_1917_, 1, v_k_1909_);
lean_ctor_set(v___x_1917_, 0, v___x_1781_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_l_1872_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_l_1872_);
v___x_1921_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 4, v_l_1872_);
lean_ctor_set(v___x_1912_, 2, v_v_1288_);
lean_ctor_set(v___x_1912_, 1, v_k_1287_);
lean_ctor_set(v___x_1912_, 0, v___x_1781_);
v___x_1923_ = v___x_1912_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_l_1872_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_l_1872_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___x_1923_);
lean_ctor_set(v___x_1292_, 3, v___x_1921_);
lean_ctor_set(v___x_1292_, 2, v_v_1915_);
lean_ctor_set(v___x_1292_, 1, v_k_1914_);
lean_ctor_set(v___x_1292_, 0, v___x_1919_);
v___x_1925_ = v___x_1292_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_k_1914_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_v_1915_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(2u);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_r_1908_);
lean_ctor_set(v___x_1292_, 0, v___x_1937_);
v___x_1939_ = v___x_1292_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_r_1908_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v___x_1942_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v_l_1289_);
lean_ctor_set(v___x_1292_, 0, v___x_1781_);
v___x_1942_ = v___x_1292_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_l_1289_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v_l_1289_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
}
else
{
return v_t_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1946_, lean_object* v_t_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1946_, v_t_1947_);
lean_dec_ref(v_k_1946_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1949_, lean_object* v_s_1950_){
_start:
{
lean_object* v_toRing_1951_; lean_object* v_invFn_x3f_1952_; lean_object* v_semiringId_x3f_1953_; lean_object* v_commSemiringInst_1954_; lean_object* v_commRingInst_1955_; lean_object* v_noZeroDivInst_x3f_1956_; lean_object* v_fieldInst_x3f_1957_; lean_object* v_powIdentityInst_x3f_1958_; lean_object* v_denoteEntries_1959_; lean_object* v_nextId_1960_; lean_object* v_steps_1961_; lean_object* v_queue_1962_; lean_object* v_basis_1963_; lean_object* v_diseqs_1964_; uint8_t v_recheck_1965_; lean_object* v_invSet_1966_; lean_object* v_powIdentityVarCount_1967_; lean_object* v_numEq0_x3f_1968_; uint8_t v_numEq0Updated_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_toRing_1951_ = lean_ctor_get(v_s_1950_, 0);
v_invFn_x3f_1952_ = lean_ctor_get(v_s_1950_, 1);
v_semiringId_x3f_1953_ = lean_ctor_get(v_s_1950_, 2);
v_commSemiringInst_1954_ = lean_ctor_get(v_s_1950_, 3);
v_commRingInst_1955_ = lean_ctor_get(v_s_1950_, 4);
v_noZeroDivInst_x3f_1956_ = lean_ctor_get(v_s_1950_, 5);
v_fieldInst_x3f_1957_ = lean_ctor_get(v_s_1950_, 6);
v_powIdentityInst_x3f_1958_ = lean_ctor_get(v_s_1950_, 7);
v_denoteEntries_1959_ = lean_ctor_get(v_s_1950_, 8);
v_nextId_1960_ = lean_ctor_get(v_s_1950_, 9);
v_steps_1961_ = lean_ctor_get(v_s_1950_, 10);
v_queue_1962_ = lean_ctor_get(v_s_1950_, 11);
v_basis_1963_ = lean_ctor_get(v_s_1950_, 12);
v_diseqs_1964_ = lean_ctor_get(v_s_1950_, 13);
v_recheck_1965_ = lean_ctor_get_uint8(v_s_1950_, sizeof(void*)*17);
v_invSet_1966_ = lean_ctor_get(v_s_1950_, 14);
v_powIdentityVarCount_1967_ = lean_ctor_get(v_s_1950_, 15);
v_numEq0_x3f_1968_ = lean_ctor_get(v_s_1950_, 16);
v_numEq0Updated_1969_ = lean_ctor_get_uint8(v_s_1950_, sizeof(void*)*17 + 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_s_1950_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1971_ = v_s_1950_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_numEq0_x3f_1968_);
lean_inc(v_powIdentityVarCount_1967_);
lean_inc(v_invSet_1966_);
lean_inc(v_diseqs_1964_);
lean_inc(v_basis_1963_);
lean_inc(v_queue_1962_);
lean_inc(v_steps_1961_);
lean_inc(v_nextId_1960_);
lean_inc(v_denoteEntries_1959_);
lean_inc(v_powIdentityInst_x3f_1958_);
lean_inc(v_fieldInst_x3f_1957_);
lean_inc(v_noZeroDivInst_x3f_1956_);
lean_inc(v_commRingInst_1955_);
lean_inc(v_commSemiringInst_1954_);
lean_inc(v_semiringId_x3f_1953_);
lean_inc(v_invFn_x3f_1952_);
lean_inc(v_toRing_1951_);
lean_dec(v_s_1950_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1949_, v_queue_1962_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 11, v___x_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_toRing_1951_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_invFn_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_semiringId_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_commSemiringInst_1954_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v_commRingInst_1955_);
lean_ctor_set(v_reuseFailAlloc_1976_, 5, v_noZeroDivInst_x3f_1956_);
lean_ctor_set(v_reuseFailAlloc_1976_, 6, v_fieldInst_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1976_, 7, v_powIdentityInst_x3f_1958_);
lean_ctor_set(v_reuseFailAlloc_1976_, 8, v_denoteEntries_1959_);
lean_ctor_set(v_reuseFailAlloc_1976_, 9, v_nextId_1960_);
lean_ctor_set(v_reuseFailAlloc_1976_, 10, v_steps_1961_);
lean_ctor_set(v_reuseFailAlloc_1976_, 11, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1976_, 12, v_basis_1963_);
lean_ctor_set(v_reuseFailAlloc_1976_, 13, v_diseqs_1964_);
lean_ctor_set(v_reuseFailAlloc_1976_, 14, v_invSet_1966_);
lean_ctor_set(v_reuseFailAlloc_1976_, 15, v_powIdentityVarCount_1967_);
lean_ctor_set(v_reuseFailAlloc_1976_, 16, v_numEq0_x3f_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*17, v_recheck_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*17 + 1, v_numEq0Updated_1969_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1978_, lean_object* v_s_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1978_, v_s_1979_);
lean_dec_ref(v_val_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2033_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2033_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2033_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_queue_1998_; lean_object* v___x_1999_; 
v_queue_1998_ = lean_ctor_get(v_a_1994_, 11);
lean_inc(v_queue_1998_);
lean_dec(v_a_1994_);
v___x_1999_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1998_);
lean_dec(v_queue_1998_);
if (lean_obj_tag(v___x_1999_) == 1)
{
lean_object* v_val_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; 
lean_del_object(v___x_1996_);
v_val_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_val_2000_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2001_, 0, v_val_2000_);
v___x_2002_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2001_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec_ref_known(v___x_2002_, 1);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2003_, v_a_1982_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v___x_2004_, 0);
lean_dec(v_unused_2012_);
v___x_2006_ = v___x_2004_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v___x_2004_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_1999_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1999_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref_known(v___x_1999_, 1);
v_a_2013_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2004_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2004_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref_known(v___x_1999_, 1);
v_a_2021_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2002_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2002_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_dec(v___x_1999_);
v___x_2029_ = lean_box(0);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2029_);
v___x_2031_ = v___x_1996_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_a_2034_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1993_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1993_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2055_, lean_object* v_k_2056_, lean_object* v_t_2057_, lean_object* v_h_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2056_, v_t_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2060_, lean_object* v_k_2061_, lean_object* v_t_2062_, lean_object* v_h_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2060_, v_k_2061_, v_t_2062_, v_h_2063_);
lean_dec_ref(v_k_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v_ks_2069_; lean_object* v_vs_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2096_; 
v_ks_2069_ = lean_ctor_get(v_x_2065_, 0);
v_vs_2070_ = lean_ctor_get(v_x_2065_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2065_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2072_ = v_x_2065_;
v_isShared_2073_ = v_isSharedCheck_2096_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_vs_2070_);
lean_inc(v_ks_2069_);
lean_dec(v_x_2065_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2096_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_array_get_size(v_ks_2069_);
v___x_2075_ = lean_nat_dec_lt(v_x_2066_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
lean_dec(v_x_2066_);
v___x_2076_ = lean_array_push(v_ks_2069_, v_x_2067_);
v___x_2077_ = lean_array_push(v_vs_2070_, v_x_2068_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2077_);
lean_ctor_set(v___x_2072_, 0, v___x_2076_);
v___x_2079_ = v___x_2072_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
else
{
lean_object* v_k_x27_2081_; size_t v___x_2082_; size_t v___x_2083_; uint8_t v___x_2084_; 
v_k_x27_2081_ = lean_array_fget_borrowed(v_ks_2069_, v_x_2066_);
v___x_2082_ = lean_ptr_addr(v_x_2067_);
v___x_2083_ = lean_ptr_addr(v_k_x27_2081_);
v___x_2084_ = lean_usize_dec_eq(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2086_; 
if (v_isShared_2073_ == 0)
{
v___x_2086_ = v___x_2072_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_ks_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_vs_2070_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = lean_nat_add(v_x_2066_, v___x_2087_);
lean_dec(v_x_2066_);
v_x_2065_ = v___x_2086_;
v_x_2066_ = v___x_2088_;
goto _start;
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2091_ = lean_array_fset(v_ks_2069_, v_x_2066_, v_x_2067_);
v___x_2092_ = lean_array_fset(v_vs_2070_, v_x_2066_, v_x_2068_);
lean_dec(v_x_2066_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2092_);
lean_ctor_set(v___x_2072_, 0, v___x_2091_);
v___x_2094_ = v___x_2072_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2097_, lean_object* v_k_2098_, lean_object* v_v_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2097_, v___x_2100_, v_k_2098_, v_v_2099_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2103_, size_t v_x_2104_, size_t v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v_es_2108_; size_t v___x_2109_; size_t v___x_2110_; lean_object* v_j_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_es_2108_ = lean_ctor_get(v_x_2103_, 0);
v___x_2109_ = ((size_t)31ULL);
v___x_2110_ = lean_usize_land(v_x_2104_, v___x_2109_);
v_j_2111_ = lean_usize_to_nat(v___x_2110_);
v___x_2112_ = lean_array_get_size(v_es_2108_);
v___x_2113_ = lean_nat_dec_lt(v_j_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec(v_j_2111_);
lean_dec(v_x_2107_);
lean_dec_ref(v_x_2106_);
return v_x_2103_;
}
else
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2154_; 
lean_inc_ref(v_es_2108_);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2103_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_x_2103_, 0);
lean_dec(v_unused_2155_);
v___x_2115_ = v_x_2103_;
v_isShared_2116_ = v_isSharedCheck_2154_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v_x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2154_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_v_2117_; lean_object* v___x_2118_; lean_object* v_xs_x27_2119_; lean_object* v___y_2121_; 
v_v_2117_ = lean_array_fget(v_es_2108_, v_j_2111_);
v___x_2118_ = lean_box(0);
v_xs_x27_2119_ = lean_array_fset(v_es_2108_, v_j_2111_, v___x_2118_);
switch(lean_obj_tag(v_v_2117_))
{
case 0:
{
lean_object* v_key_2126_; lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2139_; 
v_key_2126_ = lean_ctor_get(v_v_2117_, 0);
v_val_2127_ = lean_ctor_get(v_v_2117_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_v_2117_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2129_ = v_v_2117_;
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_inc(v_key_2126_);
lean_dec(v_v_2117_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
size_t v___x_2131_; size_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2131_ = lean_ptr_addr(v_x_2106_);
v___x_2132_ = lean_ptr_addr(v_key_2126_);
v___x_2133_ = lean_usize_dec_eq(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_del_object(v___x_2129_);
v___x_2134_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2126_, v_val_2127_, v_x_2106_, v_x_2107_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___y_2121_ = v___x_2135_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2137_; 
lean_dec(v_val_2127_);
lean_dec(v_key_2126_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_x_2107_);
lean_ctor_set(v___x_2129_, 0, v_x_2106_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_x_2106_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_x_2107_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
v___y_2121_ = v___x_2137_;
goto v___jp_2120_;
}
}
}
}
case 1:
{
lean_object* v_node_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2152_; 
v_node_2140_ = lean_ctor_get(v_v_2117_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_v_2117_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2142_ = v_v_2117_;
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_node_2140_);
lean_dec(v_v_2117_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
size_t v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2144_ = ((size_t)5ULL);
v___x_2145_ = lean_usize_shift_right(v_x_2104_, v___x_2144_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_x_2105_, v___x_2146_);
v___x_2148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2140_, v___x_2145_, v___x_2147_, v_x_2106_, v_x_2107_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2148_);
v___x_2150_ = v___x_2142_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
v___y_2121_ = v___x_2150_;
goto v___jp_2120_;
}
}
}
default: 
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_x_2106_);
lean_ctor_set(v___x_2153_, 1, v_x_2107_);
v___y_2121_ = v___x_2153_;
goto v___jp_2120_;
}
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_array_fset(v_xs_x27_2119_, v_j_2111_, v___y_2121_);
lean_dec(v_j_2111_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2122_);
v___x_2124_ = v___x_2115_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
else
{
lean_object* v_ks_2156_; lean_object* v_vs_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2177_; 
v_ks_2156_ = lean_ctor_get(v_x_2103_, 0);
v_vs_2157_ = lean_ctor_get(v_x_2103_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_x_2103_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2159_ = v_x_2103_;
v_isShared_2160_ = v_isSharedCheck_2177_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_vs_2157_);
lean_inc(v_ks_2156_);
lean_dec(v_x_2103_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2177_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_ks_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_vs_2157_);
v___x_2162_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v_newNode_2163_; uint8_t v___y_2165_; size_t v___x_2171_; uint8_t v___x_2172_; 
v_newNode_2163_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2162_, v_x_2106_, v_x_2107_);
v___x_2171_ = ((size_t)7ULL);
v___x_2172_ = lean_usize_dec_le(v___x_2171_, v_x_2105_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2163_);
v___x_2174_ = lean_unsigned_to_nat(4u);
v___x_2175_ = lean_nat_dec_lt(v___x_2173_, v___x_2174_);
lean_dec(v___x_2173_);
v___y_2165_ = v___x_2175_;
goto v___jp_2164_;
}
else
{
v___y_2165_ = v___x_2172_;
goto v___jp_2164_;
}
v___jp_2164_:
{
if (v___y_2165_ == 0)
{
lean_object* v_ks_2166_; lean_object* v_vs_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_ks_2166_ = lean_ctor_get(v_newNode_2163_, 0);
lean_inc_ref(v_ks_2166_);
v_vs_2167_ = lean_ctor_get(v_newNode_2163_, 1);
lean_inc_ref(v_vs_2167_);
lean_dec_ref(v_newNode_2163_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2105_, v_ks_2166_, v_vs_2167_, v___x_2168_, v___x_2169_);
lean_dec_ref(v_vs_2167_);
lean_dec_ref(v_ks_2166_);
return v___x_2170_;
}
else
{
return v_newNode_2163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2178_, lean_object* v_keys_2179_, lean_object* v_vals_2180_, lean_object* v_i_2181_, lean_object* v_entries_2182_){
_start:
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_array_get_size(v_keys_2179_);
v___x_2184_ = lean_nat_dec_lt(v_i_2181_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec(v_i_2181_);
return v_entries_2182_;
}
else
{
lean_object* v_k_2185_; lean_object* v_v_2186_; size_t v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; uint64_t v___x_2190_; size_t v_h_2191_; size_t v___x_2192_; lean_object* v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; size_t v_h_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_k_2185_ = lean_array_fget_borrowed(v_keys_2179_, v_i_2181_);
v_v_2186_ = lean_array_fget_borrowed(v_vals_2180_, v_i_2181_);
v___x_2187_ = lean_ptr_addr(v_k_2185_);
v___x_2188_ = ((size_t)3ULL);
v___x_2189_ = lean_usize_shift_right(v___x_2187_, v___x_2188_);
v___x_2190_ = lean_usize_to_uint64(v___x_2189_);
v_h_2191_ = lean_uint64_to_usize(v___x_2190_);
v___x_2192_ = ((size_t)5ULL);
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_sub(v_depth_2178_, v___x_2194_);
v___x_2196_ = lean_usize_mul(v___x_2192_, v___x_2195_);
v_h_2197_ = lean_usize_shift_right(v_h_2191_, v___x_2196_);
v___x_2198_ = lean_nat_add(v_i_2181_, v___x_2193_);
lean_dec(v_i_2181_);
lean_inc(v_v_2186_);
lean_inc(v_k_2185_);
v___x_2199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2182_, v_h_2197_, v_depth_2178_, v_k_2185_, v_v_2186_);
v_i_2181_ = v___x_2198_;
v_entries_2182_ = v___x_2199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2201_, lean_object* v_keys_2202_, lean_object* v_vals_2203_, lean_object* v_i_2204_, lean_object* v_entries_2205_){
_start:
{
size_t v_depth_boxed_2206_; lean_object* v_res_2207_; 
v_depth_boxed_2206_ = lean_unbox_usize(v_depth_2201_);
lean_dec(v_depth_2201_);
v_res_2207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2206_, v_keys_2202_, v_vals_2203_, v_i_2204_, v_entries_2205_);
lean_dec_ref(v_vals_2203_);
lean_dec_ref(v_keys_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v_x_2212_){
_start:
{
size_t v_x_7265__boxed_2213_; size_t v_x_7266__boxed_2214_; lean_object* v_res_2215_; 
v_x_7265__boxed_2213_ = lean_unbox_usize(v_x_2209_);
lean_dec(v_x_2209_);
v_x_7266__boxed_2214_ = lean_unbox_usize(v_x_2210_);
lean_dec(v_x_2210_);
v_res_2215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2208_, v_x_7265__boxed_2213_, v_x_7266__boxed_2214_, v_x_2211_, v_x_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; uint64_t v___x_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
v___x_2219_ = lean_ptr_addr(v_x_2217_);
v___x_2220_ = ((size_t)3ULL);
v___x_2221_ = lean_usize_shift_right(v___x_2219_, v___x_2220_);
v___x_2222_ = lean_usize_to_uint64(v___x_2221_);
v___x_2223_ = lean_uint64_to_usize(v___x_2222_);
v___x_2224_ = ((size_t)1ULL);
v___x_2225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2216_, v___x_2223_, v___x_2224_, v_x_2217_, v_x_2218_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2226_, lean_object* v_ringId_2227_, lean_object* v_s_2228_){
_start:
{
lean_object* v_rings_2229_; lean_object* v_typeIdOf_2230_; lean_object* v_exprToRingId_2231_; lean_object* v_semirings_2232_; lean_object* v_stypeIdOf_2233_; lean_object* v_exprToSemiringId_2234_; lean_object* v_ncRings_2235_; lean_object* v_exprToNCRingId_2236_; lean_object* v_nctypeIdOf_2237_; lean_object* v_ncSemirings_2238_; lean_object* v_exprToNCSemiringId_2239_; lean_object* v_ncstypeIdOf_2240_; lean_object* v_steps_2241_; uint8_t v_reportedMaxDegreeIssue_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_rings_2229_ = lean_ctor_get(v_s_2228_, 0);
v_typeIdOf_2230_ = lean_ctor_get(v_s_2228_, 1);
v_exprToRingId_2231_ = lean_ctor_get(v_s_2228_, 2);
v_semirings_2232_ = lean_ctor_get(v_s_2228_, 3);
v_stypeIdOf_2233_ = lean_ctor_get(v_s_2228_, 4);
v_exprToSemiringId_2234_ = lean_ctor_get(v_s_2228_, 5);
v_ncRings_2235_ = lean_ctor_get(v_s_2228_, 6);
v_exprToNCRingId_2236_ = lean_ctor_get(v_s_2228_, 7);
v_nctypeIdOf_2237_ = lean_ctor_get(v_s_2228_, 8);
v_ncSemirings_2238_ = lean_ctor_get(v_s_2228_, 9);
v_exprToNCSemiringId_2239_ = lean_ctor_get(v_s_2228_, 10);
v_ncstypeIdOf_2240_ = lean_ctor_get(v_s_2228_, 11);
v_steps_2241_ = lean_ctor_get(v_s_2228_, 12);
v_reportedMaxDegreeIssue_2242_ = lean_ctor_get_uint8(v_s_2228_, sizeof(void*)*13);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_s_2228_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v_s_2228_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_steps_2241_);
lean_inc(v_ncstypeIdOf_2240_);
lean_inc(v_exprToNCSemiringId_2239_);
lean_inc(v_ncSemirings_2238_);
lean_inc(v_nctypeIdOf_2237_);
lean_inc(v_exprToNCRingId_2236_);
lean_inc(v_ncRings_2235_);
lean_inc(v_exprToSemiringId_2234_);
lean_inc(v_stypeIdOf_2233_);
lean_inc(v_semirings_2232_);
lean_inc(v_exprToRingId_2231_);
lean_inc(v_typeIdOf_2230_);
lean_inc(v_rings_2229_);
lean_dec(v_s_2228_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2231_, v_e_2226_, v_ringId_2227_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 2, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_rings_2229_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_typeIdOf_2230_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_semirings_2232_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_stypeIdOf_2233_);
lean_ctor_set(v_reuseFailAlloc_2249_, 5, v_exprToSemiringId_2234_);
lean_ctor_set(v_reuseFailAlloc_2249_, 6, v_ncRings_2235_);
lean_ctor_set(v_reuseFailAlloc_2249_, 7, v_exprToNCRingId_2236_);
lean_ctor_set(v_reuseFailAlloc_2249_, 8, v_nctypeIdOf_2237_);
lean_ctor_set(v_reuseFailAlloc_2249_, 9, v_ncSemirings_2238_);
lean_ctor_set(v_reuseFailAlloc_2249_, 10, v_exprToNCSemiringId_2239_);
lean_ctor_set(v_reuseFailAlloc_2249_, 11, v_ncstypeIdOf_2240_);
lean_ctor_set(v_reuseFailAlloc_2249_, 12, v_steps_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2249_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2242_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2254_, v_a_2256_, v_a_2261_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
if (lean_obj_tag(v_a_2268_) == 1)
{
lean_object* v_ringId_2269_; lean_object* v_val_2270_; uint8_t v___x_2271_; 
v_ringId_2269_ = lean_ctor_get(v_a_2255_, 0);
v_val_2270_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_val_2270_);
lean_dec_ref_known(v_a_2268_, 1);
v___x_2271_ = lean_nat_dec_eq(v_val_2270_, v_ringId_2269_);
lean_dec(v_val_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2257_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; uint8_t v_verbose_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v_verbose_2274_ = lean_ctor_get_uint8(v_a_2273_, 0);
lean_dec(v_a_2273_);
if (v_verbose_2274_ == 0)
{
lean_dec_ref(v_e_2254_);
goto v___jp_2264_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2276_ = l_Lean_indentExpr(v_e_2254_);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_Meta_Sym_reportIssue(v___x_2277_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_dec_ref_known(v___x_2278_, 1);
goto v___jp_2264_;
}
else
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_e_2254_);
v_a_2279_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2272_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2272_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_dec_ref(v_e_2254_);
goto v___jp_2264_;
}
}
else
{
lean_object* v_ringId_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec(v_a_2268_);
v_ringId_2287_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_ringId_2287_);
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2288_, 0, v_e_2254_);
lean_closure_set(v___f_2288_, 1, v_ringId_2287_);
v___x_2289_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2290_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2289_, v___f_2288_, v_a_2256_);
return v___x_2290_;
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_e_2254_);
v_a_2291_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2267_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2267_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
v___jp_2264_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2310_, v_a_2311_, v_a_2312_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, size_t v_x_2345_, size_t v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
size_t v_x_7555__boxed_2356_; size_t v_x_7556__boxed_2357_; lean_object* v_res_2358_; 
v_x_7555__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_x_7556__boxed_2357_ = lean_unbox_usize(v_x_2353_);
lean_dec(v_x_2353_);
v_res_2358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2350_, v_x_2351_, v_x_7555__boxed_2356_, v_x_7556__boxed_2357_, v_x_2354_, v_x_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2359_, lean_object* v_n_2360_, lean_object* v_k_2361_, lean_object* v_v_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2360_, v_k_2361_, v_v_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2364_, size_t v_depth_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_entries_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2365_, v_keys_2366_, v_vals_2367_, v_i_2369_, v_entries_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_depth_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_entries_2378_){
_start:
{
size_t v_depth_boxed_2379_; lean_object* v_res_2380_; 
v_depth_boxed_2379_ = lean_unbox_usize(v_depth_2373_);
lean_dec(v_depth_2373_);
v_res_2380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2372_, v_depth_boxed_2379_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_entries_2378_);
lean_dec_ref(v_vals_2375_);
lean_dec_ref(v_keys_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2387_, lean_object* v___f_2388_, lean_object* v___f_2389_, lean_object* v_size_2390_, lean_object* v_s_2391_){
_start:
{
lean_object* v_id_2392_; lean_object* v_type_2393_; lean_object* v_u_2394_; lean_object* v_ringInst_2395_; lean_object* v_semiringInst_2396_; lean_object* v_charInst_x3f_2397_; lean_object* v_addFn_x3f_2398_; lean_object* v_mulFn_x3f_2399_; lean_object* v_subFn_x3f_2400_; lean_object* v_negFn_x3f_2401_; lean_object* v_powFn_x3f_2402_; lean_object* v_intCastFn_x3f_2403_; lean_object* v_natCastFn_x3f_2404_; lean_object* v_one_x3f_2405_; lean_object* v_vars_2406_; lean_object* v_varMap_2407_; lean_object* v_denote_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2417_; 
v_id_2392_ = lean_ctor_get(v_s_2391_, 0);
v_type_2393_ = lean_ctor_get(v_s_2391_, 1);
v_u_2394_ = lean_ctor_get(v_s_2391_, 2);
v_ringInst_2395_ = lean_ctor_get(v_s_2391_, 3);
v_semiringInst_2396_ = lean_ctor_get(v_s_2391_, 4);
v_charInst_x3f_2397_ = lean_ctor_get(v_s_2391_, 5);
v_addFn_x3f_2398_ = lean_ctor_get(v_s_2391_, 6);
v_mulFn_x3f_2399_ = lean_ctor_get(v_s_2391_, 7);
v_subFn_x3f_2400_ = lean_ctor_get(v_s_2391_, 8);
v_negFn_x3f_2401_ = lean_ctor_get(v_s_2391_, 9);
v_powFn_x3f_2402_ = lean_ctor_get(v_s_2391_, 10);
v_intCastFn_x3f_2403_ = lean_ctor_get(v_s_2391_, 11);
v_natCastFn_x3f_2404_ = lean_ctor_get(v_s_2391_, 12);
v_one_x3f_2405_ = lean_ctor_get(v_s_2391_, 13);
v_vars_2406_ = lean_ctor_get(v_s_2391_, 14);
v_varMap_2407_ = lean_ctor_get(v_s_2391_, 15);
v_denote_2408_ = lean_ctor_get(v_s_2391_, 16);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_s_2391_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2410_ = v_s_2391_;
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_denote_2408_);
lean_inc(v_varMap_2407_);
lean_inc(v_vars_2406_);
lean_inc(v_one_x3f_2405_);
lean_inc(v_natCastFn_x3f_2404_);
lean_inc(v_intCastFn_x3f_2403_);
lean_inc(v_powFn_x3f_2402_);
lean_inc(v_negFn_x3f_2401_);
lean_inc(v_subFn_x3f_2400_);
lean_inc(v_mulFn_x3f_2399_);
lean_inc(v_addFn_x3f_2398_);
lean_inc(v_charInst_x3f_2397_);
lean_inc(v_semiringInst_2396_);
lean_inc(v_ringInst_2395_);
lean_inc(v_u_2394_);
lean_inc(v_type_2393_);
lean_inc(v_id_2392_);
lean_dec(v_s_2391_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2417_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_inc_ref(v_e_2387_);
v___x_2412_ = l_Lean_PersistentArray_push___redArg(v_vars_2406_, v_e_2387_);
v___x_2413_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2388_, v___f_2389_, v_varMap_2407_, v_e_2387_, v_size_2390_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 15, v___x_2413_);
lean_ctor_set(v___x_2410_, 14, v___x_2412_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_id_2392_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_type_2393_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_u_2394_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_ringInst_2395_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_semiringInst_2396_);
lean_ctor_set(v_reuseFailAlloc_2416_, 5, v_charInst_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2416_, 6, v_addFn_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2416_, 7, v_mulFn_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2416_, 8, v_subFn_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2416_, 9, v_negFn_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2416_, 10, v_powFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2416_, 11, v_intCastFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2416_, 12, v_natCastFn_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2416_, 13, v_one_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2416_, 14, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 15, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2416_, 16, v_denote_2408_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2418_, lean_object* v_size_2419_, lean_object* v_____r_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_apply_2(v_toPure_2418_, lean_box(0), v_size_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2422_, lean_object* v_inst_2423_, lean_object* v_toBind_2424_, lean_object* v___f_2425_, lean_object* v_____r_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2427_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2428_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2428_, 0, lean_box(0));
lean_closure_set(v___x_2428_, 1, v___x_2427_);
lean_closure_set(v___x_2428_, 2, v_e_2422_);
v___x_2429_ = lean_apply_2(v_inst_2423_, lean_box(0), v___x_2428_);
v___x_2430_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v___x_2429_, v___f_2425_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2431_, lean_object* v_e_2432_, lean_object* v_toBind_2433_, lean_object* v___f_2434_, lean_object* v_____r_2435_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_apply_1(v_inst_2431_, v_e_2432_);
v___x_2437_ = lean_apply_4(v_toBind_2433_, lean_box(0), lean_box(0), v___x_2436_, v___f_2434_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2438_, lean_object* v___f_2439_, lean_object* v_e_2440_, lean_object* v_toPure_2441_, lean_object* v_inst_2442_, lean_object* v_toBind_2443_, lean_object* v_inst_2444_, lean_object* v_modifyRing_2445_, lean_object* v_s_2446_){
_start:
{
lean_object* v_vars_2447_; lean_object* v_varMap_2448_; lean_object* v___x_2449_; 
v_vars_2447_ = lean_ctor_get(v_s_2446_, 14);
lean_inc_ref(v_vars_2447_);
v_varMap_2448_ = lean_ctor_get(v_s_2446_, 15);
lean_inc_ref(v_varMap_2448_);
lean_dec_ref(v_s_2446_);
lean_inc_ref(v_e_2440_);
lean_inc_ref(v___f_2439_);
lean_inc_ref(v___f_2438_);
v___x_2449_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2438_, v___f_2439_, v_varMap_2448_, v_e_2440_);
lean_dec_ref(v_varMap_2448_);
if (lean_obj_tag(v___x_2449_) == 1)
{
lean_object* v_val_2450_; lean_object* v___x_2451_; 
lean_dec_ref(v_vars_2447_);
lean_dec(v_modifyRing_2445_);
lean_dec(v_inst_2444_);
lean_dec(v_toBind_2443_);
lean_dec(v_inst_2442_);
lean_dec_ref(v_e_2440_);
lean_dec_ref(v___f_2439_);
lean_dec_ref(v___f_2438_);
v_val_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = lean_apply_2(v_toPure_2441_, lean_box(0), v_val_2450_);
return v___x_2451_;
}
else
{
lean_object* v_size_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v___x_2449_);
v_size_2452_ = lean_ctor_get(v_vars_2447_, 2);
lean_inc_n(v_size_2452_, 2);
lean_dec_ref(v_vars_2447_);
lean_inc_ref_n(v_e_2440_, 2);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2453_, 0, v_e_2440_);
lean_closure_set(v___f_2453_, 1, v___f_2438_);
lean_closure_set(v___f_2453_, 2, v___f_2439_);
lean_closure_set(v___f_2453_, 3, v_size_2452_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2454_, 0, v_toPure_2441_);
lean_closure_set(v___f_2454_, 1, v_size_2452_);
lean_inc_n(v_toBind_2443_, 2);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2455_, 0, v_e_2440_);
lean_closure_set(v___f_2455_, 1, v_inst_2442_);
lean_closure_set(v___f_2455_, 2, v_toBind_2443_);
lean_closure_set(v___f_2455_, 3, v___f_2454_);
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2456_, 0, v_inst_2444_);
lean_closure_set(v___f_2456_, 1, v_e_2440_);
lean_closure_set(v___f_2456_, 2, v_toBind_2443_);
lean_closure_set(v___f_2456_, 3, v___f_2455_);
v___x_2457_ = lean_apply_1(v_modifyRing_2445_, v___f_2453_);
v___x_2458_ = lean_apply_4(v_toBind_2443_, lean_box(0), lean_box(0), v___x_2457_, v___f_2456_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_e_2465_){
_start:
{
lean_object* v_toApplicative_2466_; lean_object* v_toBind_2467_; lean_object* v_getRing_2468_; lean_object* v_modifyRing_2469_; lean_object* v_toPure_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; 
v_toApplicative_2466_ = lean_ctor_get(v_inst_2462_, 0);
lean_inc_ref(v_toApplicative_2466_);
v_toBind_2467_ = lean_ctor_get(v_inst_2462_, 1);
lean_inc_n(v_toBind_2467_, 2);
lean_dec_ref(v_inst_2462_);
v_getRing_2468_ = lean_ctor_get(v_inst_2463_, 0);
lean_inc(v_getRing_2468_);
v_modifyRing_2469_ = lean_ctor_get(v_inst_2463_, 1);
lean_inc(v_modifyRing_2469_);
lean_dec_ref(v_inst_2463_);
v_toPure_2470_ = lean_ctor_get(v_toApplicative_2466_, 1);
lean_inc(v_toPure_2470_);
lean_dec_ref(v_toApplicative_2466_);
v___f_2471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2473_, 0, v___f_2471_);
lean_closure_set(v___f_2473_, 1, v___f_2472_);
lean_closure_set(v___f_2473_, 2, v_e_2465_);
lean_closure_set(v___f_2473_, 3, v_toPure_2470_);
lean_closure_set(v___f_2473_, 4, v_inst_2461_);
lean_closure_set(v___f_2473_, 5, v_toBind_2467_);
lean_closure_set(v___f_2473_, 6, v_inst_2464_);
lean_closure_set(v___f_2473_, 7, v_modifyRing_2469_);
v___x_2474_ = lean_apply_4(v_toBind_2467_, lean_box(0), lean_box(0), v_getRing_2468_, v___f_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_e_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2476_, v_inst_2477_, v_inst_2478_, v_inst_2479_, v_e_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2482_, v___y_2483_, v___y_2484_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2512_, lean_object* v_size_2513_, lean_object* v_s_2514_){
_start:
{
lean_object* v_toRing_2515_; lean_object* v_invFn_x3f_2516_; lean_object* v_semiringId_x3f_2517_; lean_object* v_commSemiringInst_2518_; lean_object* v_commRingInst_2519_; lean_object* v_noZeroDivInst_x3f_2520_; lean_object* v_fieldInst_x3f_2521_; lean_object* v_powIdentityInst_x3f_2522_; lean_object* v_denoteEntries_2523_; lean_object* v_nextId_2524_; lean_object* v_steps_2525_; lean_object* v_queue_2526_; lean_object* v_basis_2527_; lean_object* v_diseqs_2528_; uint8_t v_recheck_2529_; lean_object* v_invSet_2530_; lean_object* v_powIdentityVarCount_2531_; lean_object* v_numEq0_x3f_2532_; uint8_t v_numEq0Updated_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2566_; 
v_toRing_2515_ = lean_ctor_get(v_s_2514_, 0);
v_invFn_x3f_2516_ = lean_ctor_get(v_s_2514_, 1);
v_semiringId_x3f_2517_ = lean_ctor_get(v_s_2514_, 2);
v_commSemiringInst_2518_ = lean_ctor_get(v_s_2514_, 3);
v_commRingInst_2519_ = lean_ctor_get(v_s_2514_, 4);
v_noZeroDivInst_x3f_2520_ = lean_ctor_get(v_s_2514_, 5);
v_fieldInst_x3f_2521_ = lean_ctor_get(v_s_2514_, 6);
v_powIdentityInst_x3f_2522_ = lean_ctor_get(v_s_2514_, 7);
v_denoteEntries_2523_ = lean_ctor_get(v_s_2514_, 8);
v_nextId_2524_ = lean_ctor_get(v_s_2514_, 9);
v_steps_2525_ = lean_ctor_get(v_s_2514_, 10);
v_queue_2526_ = lean_ctor_get(v_s_2514_, 11);
v_basis_2527_ = lean_ctor_get(v_s_2514_, 12);
v_diseqs_2528_ = lean_ctor_get(v_s_2514_, 13);
v_recheck_2529_ = lean_ctor_get_uint8(v_s_2514_, sizeof(void*)*17);
v_invSet_2530_ = lean_ctor_get(v_s_2514_, 14);
v_powIdentityVarCount_2531_ = lean_ctor_get(v_s_2514_, 15);
v_numEq0_x3f_2532_ = lean_ctor_get(v_s_2514_, 16);
v_numEq0Updated_2533_ = lean_ctor_get_uint8(v_s_2514_, sizeof(void*)*17 + 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_s_2514_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2535_ = v_s_2514_;
v_isShared_2536_ = v_isSharedCheck_2566_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_numEq0_x3f_2532_);
lean_inc(v_powIdentityVarCount_2531_);
lean_inc(v_invSet_2530_);
lean_inc(v_diseqs_2528_);
lean_inc(v_basis_2527_);
lean_inc(v_queue_2526_);
lean_inc(v_steps_2525_);
lean_inc(v_nextId_2524_);
lean_inc(v_denoteEntries_2523_);
lean_inc(v_powIdentityInst_x3f_2522_);
lean_inc(v_fieldInst_x3f_2521_);
lean_inc(v_noZeroDivInst_x3f_2520_);
lean_inc(v_commRingInst_2519_);
lean_inc(v_commSemiringInst_2518_);
lean_inc(v_semiringId_x3f_2517_);
lean_inc(v_invFn_x3f_2516_);
lean_inc(v_toRing_2515_);
lean_dec(v_s_2514_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2566_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_id_2537_; lean_object* v_type_2538_; lean_object* v_u_2539_; lean_object* v_ringInst_2540_; lean_object* v_semiringInst_2541_; lean_object* v_charInst_x3f_2542_; lean_object* v_addFn_x3f_2543_; lean_object* v_mulFn_x3f_2544_; lean_object* v_subFn_x3f_2545_; lean_object* v_negFn_x3f_2546_; lean_object* v_powFn_x3f_2547_; lean_object* v_intCastFn_x3f_2548_; lean_object* v_natCastFn_x3f_2549_; lean_object* v_one_x3f_2550_; lean_object* v_vars_2551_; lean_object* v_varMap_2552_; lean_object* v_denote_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2565_; 
v_id_2537_ = lean_ctor_get(v_toRing_2515_, 0);
v_type_2538_ = lean_ctor_get(v_toRing_2515_, 1);
v_u_2539_ = lean_ctor_get(v_toRing_2515_, 2);
v_ringInst_2540_ = lean_ctor_get(v_toRing_2515_, 3);
v_semiringInst_2541_ = lean_ctor_get(v_toRing_2515_, 4);
v_charInst_x3f_2542_ = lean_ctor_get(v_toRing_2515_, 5);
v_addFn_x3f_2543_ = lean_ctor_get(v_toRing_2515_, 6);
v_mulFn_x3f_2544_ = lean_ctor_get(v_toRing_2515_, 7);
v_subFn_x3f_2545_ = lean_ctor_get(v_toRing_2515_, 8);
v_negFn_x3f_2546_ = lean_ctor_get(v_toRing_2515_, 9);
v_powFn_x3f_2547_ = lean_ctor_get(v_toRing_2515_, 10);
v_intCastFn_x3f_2548_ = lean_ctor_get(v_toRing_2515_, 11);
v_natCastFn_x3f_2549_ = lean_ctor_get(v_toRing_2515_, 12);
v_one_x3f_2550_ = lean_ctor_get(v_toRing_2515_, 13);
v_vars_2551_ = lean_ctor_get(v_toRing_2515_, 14);
v_varMap_2552_ = lean_ctor_get(v_toRing_2515_, 15);
v_denote_2553_ = lean_ctor_get(v_toRing_2515_, 16);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_toRing_2515_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2555_ = v_toRing_2515_;
v_isShared_2556_ = v_isSharedCheck_2565_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_denote_2553_);
lean_inc(v_varMap_2552_);
lean_inc(v_vars_2551_);
lean_inc(v_one_x3f_2550_);
lean_inc(v_natCastFn_x3f_2549_);
lean_inc(v_intCastFn_x3f_2548_);
lean_inc(v_powFn_x3f_2547_);
lean_inc(v_negFn_x3f_2546_);
lean_inc(v_subFn_x3f_2545_);
lean_inc(v_mulFn_x3f_2544_);
lean_inc(v_addFn_x3f_2543_);
lean_inc(v_charInst_x3f_2542_);
lean_inc(v_semiringInst_2541_);
lean_inc(v_ringInst_2540_);
lean_inc(v_u_2539_);
lean_inc(v_type_2538_);
lean_inc(v_id_2537_);
lean_dec(v_toRing_2515_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2565_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_inc_ref(v_e_2512_);
v___x_2557_ = l_Lean_PersistentArray_push___redArg(v_vars_2551_, v_e_2512_);
v___x_2558_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2552_, v_e_2512_, v_size_2513_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 15, v___x_2558_);
lean_ctor_set(v___x_2555_, 14, v___x_2557_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_id_2537_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_type_2538_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_u_2539_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_ringInst_2540_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_semiringInst_2541_);
lean_ctor_set(v_reuseFailAlloc_2564_, 5, v_charInst_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2564_, 6, v_addFn_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2564_, 7, v_mulFn_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2564_, 8, v_subFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2564_, 9, v_negFn_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2564_, 10, v_powFn_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2564_, 11, v_intCastFn_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2564_, 12, v_natCastFn_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2564_, 13, v_one_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2564_, 14, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2564_, 15, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2564_, 16, v_denote_2553_);
v___x_2560_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2562_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2560_);
v___x_2562_ = v___x_2535_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_invFn_x3f_2516_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_semiringId_x3f_2517_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_commSemiringInst_2518_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_commRingInst_2519_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_noZeroDivInst_x3f_2520_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_fieldInst_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v_powIdentityInst_x3f_2522_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v_denoteEntries_2523_);
lean_ctor_set(v_reuseFailAlloc_2563_, 9, v_nextId_2524_);
lean_ctor_set(v_reuseFailAlloc_2563_, 10, v_steps_2525_);
lean_ctor_set(v_reuseFailAlloc_2563_, 11, v_queue_2526_);
lean_ctor_set(v_reuseFailAlloc_2563_, 12, v_basis_2527_);
lean_ctor_set(v_reuseFailAlloc_2563_, 13, v_diseqs_2528_);
lean_ctor_set(v_reuseFailAlloc_2563_, 14, v_invSet_2530_);
lean_ctor_set(v_reuseFailAlloc_2563_, 15, v_powIdentityVarCount_2531_);
lean_ctor_set(v_reuseFailAlloc_2563_, 16, v_numEq0_x3f_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*17, v_recheck_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2563_, sizeof(void*)*17 + 1, v_numEq0Updated_2533_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2631_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2631_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2631_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_toRing_2585_; lean_object* v_vars_2586_; lean_object* v_varMap_2587_; lean_object* v___x_2588_; 
v_toRing_2585_ = lean_ctor_get(v_a_2581_, 0);
lean_inc_ref(v_toRing_2585_);
lean_dec(v_a_2581_);
v_vars_2586_ = lean_ctor_get(v_toRing_2585_, 14);
lean_inc_ref(v_vars_2586_);
v_varMap_2587_ = lean_ctor_get(v_toRing_2585_, 15);
lean_inc_ref(v_varMap_2587_);
lean_dec_ref(v_toRing_2585_);
v___x_2588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2587_, v_e_2567_);
lean_dec_ref(v_varMap_2587_);
if (lean_obj_tag(v___x_2588_) == 1)
{
lean_object* v_val_2589_; lean_object* v___x_2591_; 
lean_dec_ref(v_vars_2586_);
lean_dec_ref(v_e_2567_);
v_val_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_val_2589_);
lean_dec_ref_known(v___x_2588_, 1);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_val_2589_);
v___x_2591_ = v___x_2583_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_val_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
else
{
lean_object* v_size_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; 
lean_dec(v___x_2588_);
lean_del_object(v___x_2583_);
v_size_2593_ = lean_ctor_get(v_vars_2586_, 2);
lean_inc_n(v_size_2593_, 2);
lean_dec_ref(v_vars_2586_);
lean_inc_ref(v_e_2567_);
v___f_2594_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2594_, 0, v_e_2567_);
lean_closure_set(v___f_2594_, 1, v_size_2593_);
v___x_2595_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2594_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; 
lean_dec_ref_known(v___x_2595_, 1);
lean_inc_ref(v_e_2567_);
v___x_2596_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2567_, v___y_2568_, v___y_2569_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec_ref_known(v___x_2596_, 1);
v___x_2597_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2598_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2597_, v_e_2567_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2598_, 0);
lean_dec(v_unused_2606_);
v___x_2600_ = v___x_2598_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v___x_2598_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v_size_2593_);
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_size_2593_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_size_2593_);
v_a_2607_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2598_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2598_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_size_2593_);
lean_dec_ref(v_e_2567_);
v_a_2615_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2596_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2596_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_size_2593_);
lean_dec_ref(v_e_2567_);
v_a_2623_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2595_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2595_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_e_2567_);
v_a_2632_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2580_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2580_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2681_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
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
