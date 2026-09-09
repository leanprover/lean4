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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
uint8_t v___x_6104__boxed_89_; lean_object* v_res_90_; 
v___x_6104__boxed_89_ = lean_unbox(v___x_87_);
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_6104__boxed_89_, v_s_88_);
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
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_toCold_478_; lean_object* v_mctx_479_; lean_object* v_lctx_480_; lean_object* v_options_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v___y_471_);
v_toCold_478_ = lean_ctor_get(v___y_472_, 0);
v_mctx_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_mctx_479_);
lean_dec(v___x_477_);
v_lctx_480_ = lean_ctor_get(v___y_470_, 2);
v_options_481_ = lean_ctor_get(v_toCold_478_, 2);
lean_inc_ref(v_options_481_);
lean_inc_ref(v_lctx_480_);
v___x_482_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_482_, 0, v_env_476_);
lean_ctor_set(v___x_482_, 1, v_mctx_479_);
lean_ctor_set(v___x_482_, 2, v_lctx_480_);
lean_ctor_set(v___x_482_, 3, v_options_481_);
v___x_483_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_msgData_469_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_ref_498_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_ref_498_ = lean_ctor_get(v___y_495_, 2);
v___x_499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_inc(v_ref_498_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_ref_498_);
lean_ctor_set(v___x_504_, 1, v_a_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 1);
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_520_, v_a_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_546_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_546_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_546_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_546_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_ringId_536_; lean_object* v_rings_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_ringId_536_ = lean_ctor_get(v_a_519_, 0);
v_rings_537_ = lean_ctor_get(v_a_532_, 0);
lean_inc_ref(v_rings_537_);
lean_dec(v_a_532_);
v___x_538_ = lean_array_get_size(v_rings_537_);
v___x_539_ = lean_nat_dec_lt(v_ringId_536_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec_ref(v_rings_537_);
lean_del_object(v___x_534_);
v___x_540_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_541_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_540_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_array_fget(v_rings_537_, v_ringId_536_);
lean_dec_ref(v_rings_537_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_542_);
v___x_544_ = v___x_534_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_531_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_531_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_568_, lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_569_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_583_, lean_object* v_msg_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_583_, v_msg_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_598_, lean_object* v_f_599_, lean_object* v_s_600_){
_start:
{
lean_object* v_rings_601_; lean_object* v_typeIdOf_602_; lean_object* v_exprToRingId_603_; lean_object* v_semirings_604_; lean_object* v_stypeIdOf_605_; lean_object* v_exprToSemiringId_606_; lean_object* v_ncRings_607_; lean_object* v_exprToNCRingId_608_; lean_object* v_nctypeIdOf_609_; lean_object* v_ncSemirings_610_; lean_object* v_exprToNCSemiringId_611_; lean_object* v_ncstypeIdOf_612_; lean_object* v_steps_613_; uint8_t v_reportedMaxDegreeIssue_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_rings_601_ = lean_ctor_get(v_s_600_, 0);
v_typeIdOf_602_ = lean_ctor_get(v_s_600_, 1);
v_exprToRingId_603_ = lean_ctor_get(v_s_600_, 2);
v_semirings_604_ = lean_ctor_get(v_s_600_, 3);
v_stypeIdOf_605_ = lean_ctor_get(v_s_600_, 4);
v_exprToSemiringId_606_ = lean_ctor_get(v_s_600_, 5);
v_ncRings_607_ = lean_ctor_get(v_s_600_, 6);
v_exprToNCRingId_608_ = lean_ctor_get(v_s_600_, 7);
v_nctypeIdOf_609_ = lean_ctor_get(v_s_600_, 8);
v_ncSemirings_610_ = lean_ctor_get(v_s_600_, 9);
v_exprToNCSemiringId_611_ = lean_ctor_get(v_s_600_, 10);
v_ncstypeIdOf_612_ = lean_ctor_get(v_s_600_, 11);
v_steps_613_ = lean_ctor_get(v_s_600_, 12);
v_reportedMaxDegreeIssue_614_ = lean_ctor_get_uint8(v_s_600_, sizeof(void*)*13);
v___x_615_ = lean_array_get_size(v_rings_601_);
v___x_616_ = lean_nat_dec_lt(v_ringId_598_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v_f_599_);
return v_s_600_;
}
else
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
lean_inc(v_steps_613_);
lean_inc_ref(v_ncstypeIdOf_612_);
lean_inc_ref(v_exprToNCSemiringId_611_);
lean_inc_ref(v_ncSemirings_610_);
lean_inc_ref(v_nctypeIdOf_609_);
lean_inc_ref(v_exprToNCRingId_608_);
lean_inc_ref(v_ncRings_607_);
lean_inc_ref(v_exprToSemiringId_606_);
lean_inc_ref(v_stypeIdOf_605_);
lean_inc_ref(v_semirings_604_);
lean_inc_ref(v_exprToRingId_603_);
lean_inc_ref(v_typeIdOf_602_);
lean_inc_ref(v_rings_601_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_s_600_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_629_ = lean_ctor_get(v_s_600_, 12);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_s_600_, 11);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_s_600_, 10);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_s_600_, 9);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_s_600_, 8);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_s_600_, 7);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_s_600_, 6);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_s_600_, 5);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_s_600_, 4);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_s_600_, 3);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_s_600_, 2);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_s_600_, 1);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_s_600_, 0);
lean_dec(v_unused_641_);
v___x_618_ = v_s_600_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_dec(v_s_600_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_v_620_; lean_object* v___x_621_; lean_object* v_xs_x27_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_v_620_ = lean_array_fget(v_rings_601_, v_ringId_598_);
v___x_621_ = lean_box(0);
v_xs_x27_622_ = lean_array_fset(v_rings_601_, v_ringId_598_, v___x_621_);
v___x_623_ = lean_apply_1(v_f_599_, v_v_620_);
v___x_624_ = lean_array_fset(v_xs_x27_622_, v_ringId_598_, v___x_623_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_624_);
v___x_626_ = v___x_618_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_typeIdOf_602_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_exprToRingId_603_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_semirings_604_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_stypeIdOf_605_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_exprToSemiringId_606_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_ncRings_607_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_exprToNCRingId_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_nctypeIdOf_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_ncSemirings_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 10, v_exprToNCSemiringId_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 11, v_ncstypeIdOf_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 12, v_steps_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_627_, sizeof(void*)*13, v_reportedMaxDegreeIssue_614_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_642_, lean_object* v_f_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_642_, v_f_643_, v_s_644_);
lean_dec(v_ringId_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_ringId_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_ringId_650_ = lean_ctor_get(v_a_647_, 0);
lean_inc(v_ringId_650_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_651_, 0, v_ringId_650_);
lean_closure_set(v___f_651_, 1, v_f_646_);
v___x_652_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_652_, v___f_651_, v_a_648_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_659_, v_a_660_, v_a_661_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_689_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_ringId_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_ringId_705_ = lean_ctor_get(v_a_693_, 0);
v___x_706_ = 1;
lean_inc(v_ringId_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_707_, 0, v_ringId_705_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v___x_706_);
lean_inc(v_a_703_);
lean_inc_ref(v_a_702_);
lean_inc(v_a_701_);
lean_inc_ref(v_a_700_);
lean_inc(v_a_699_);
lean_inc_ref(v_a_698_);
lean_inc(v_a_697_);
lean_inc_ref(v_a_696_);
lean_inc(v_a_695_);
lean_inc(v_a_694_);
v___x_708_ = lean_apply_12(v_x_692_, v___x_707_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, lean_box(0));
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_723_, lean_object* v_x_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_ringId_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_ringId_737_ = lean_ctor_get(v_a_725_, 0);
v___x_738_ = 1;
lean_inc(v_ringId_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_739_, 0, v_ringId_737_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*1, v___x_738_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
lean_inc_ref(v_a_728_);
lean_inc(v_a_727_);
lean_inc(v_a_726_);
v___x_740_ = lean_apply_12(v_x_724_, v___x_739_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, lean_box(0));
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_741_, lean_object* v_x_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_741_, v_x_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_756_){
_start:
{
uint8_t v_checkCoeffDvd_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_checkCoeffDvd_758_ = lean_ctor_get_uint8(v_a_756_, sizeof(void*)*1);
v___x_759_ = lean_box(v_checkCoeffDvd_758_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_761_);
lean_dec_ref(v_a_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_764_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_790_, lean_object* v_vals_791_, lean_object* v_i_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_keys_790_);
v___x_795_ = lean_nat_dec_lt(v_i_792_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_i_792_);
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v_k_x27_797_; size_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v_k_x27_797_ = lean_array_fget_borrowed(v_keys_790_, v_i_792_);
v___x_798_ = lean_ptr_addr(v_k_793_);
v___x_799_ = lean_ptr_addr(v_k_x27_797_);
v___x_800_ = lean_usize_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_i_792_, v___x_801_);
lean_dec(v_i_792_);
v_i_792_ = v___x_802_;
goto _start;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_array_fget_borrowed(v_vals_791_, v_i_792_);
lean_dec(v_i_792_);
lean_inc(v___x_804_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_806_, lean_object* v_vals_807_, lean_object* v_i_808_, lean_object* v_k_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_806_, v_vals_807_, v_i_808_, v_k_809_);
lean_dec_ref(v_k_809_);
lean_dec_ref(v_vals_807_);
lean_dec_ref(v_keys_806_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_811_, size_t v_x_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_es_814_; lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; lean_object* v_j_818_; lean_object* v___x_819_; 
v_es_814_ = lean_ctor_get(v_x_811_, 0);
v___x_815_ = lean_box(2);
v___x_816_ = ((size_t)31ULL);
v___x_817_ = lean_usize_land(v_x_812_, v___x_816_);
v_j_818_ = lean_usize_to_nat(v___x_817_);
v___x_819_ = lean_array_get_borrowed(v___x_815_, v_es_814_, v_j_818_);
lean_dec(v_j_818_);
switch(lean_obj_tag(v___x_819_))
{
case 0:
{
lean_object* v_key_820_; lean_object* v_val_821_; size_t v___x_822_; size_t v___x_823_; uint8_t v___x_824_; 
v_key_820_ = lean_ctor_get(v___x_819_, 0);
v_val_821_ = lean_ctor_get(v___x_819_, 1);
v___x_822_ = lean_ptr_addr(v_x_813_);
v___x_823_ = lean_ptr_addr(v_key_820_);
v___x_824_ = lean_usize_dec_eq(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
lean_inc(v_val_821_);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_val_821_);
return v___x_826_;
}
}
case 1:
{
lean_object* v_node_827_; size_t v___x_828_; size_t v___x_829_; 
v_node_827_ = lean_ctor_get(v___x_819_, 0);
v___x_828_ = ((size_t)5ULL);
v___x_829_ = lean_usize_shift_right(v_x_812_, v___x_828_);
v_x_811_ = v_node_827_;
v_x_812_ = v___x_829_;
goto _start;
}
default: 
{
lean_object* v___x_831_; 
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
}
else
{
lean_object* v_ks_832_; lean_object* v_vs_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_ks_832_ = lean_ctor_get(v_x_811_, 0);
v_vs_833_ = lean_ctor_get(v_x_811_, 1);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_832_, v_vs_833_, v___x_834_, v_x_813_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
size_t v_x_904__boxed_839_; lean_object* v_res_840_; 
v_x_904__boxed_839_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_840_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_836_, v_x_904__boxed_839_, v_x_838_);
lean_dec_ref(v_x_838_);
lean_dec_ref(v_x_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; uint64_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_843_ = lean_ptr_addr(v_x_842_);
v___x_844_ = ((size_t)3ULL);
v___x_845_ = lean_usize_shift_right(v___x_843_, v___x_844_);
v___x_846_ = lean_usize_to_uint64(v___x_845_);
v___x_847_ = lean_uint64_to_usize(v___x_846_);
v___x_848_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_841_, v___x_847_, v_x_842_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_849_, v_x_850_);
lean_dec_ref(v_x_850_);
lean_dec_ref(v_x_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_853_, v_a_854_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_866_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_866_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_exprToRingId_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v_exprToRingId_861_ = lean_ctor_get(v_a_857_, 2);
lean_inc_ref(v_exprToRingId_861_);
lean_dec(v_a_857_);
v___x_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_861_, v_e_852_);
lean_dec_ref(v_exprToRingId_861_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_856_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_856_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_875_, v_a_876_, v_a_877_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_e_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_880_, v_a_881_, v_a_889_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_e_893_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_910_, v_x_911_, v_x_912_);
lean_dec_ref(v_x_912_);
lean_dec_ref(v_x_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_914_, lean_object* v_x_915_, size_t v_x_916_, lean_object* v_x_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_915_, v_x_916_, v_x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
size_t v_x_1025__boxed_923_; lean_object* v_res_924_; 
v_x_1025__boxed_923_ = lean_unbox_usize(v_x_921_);
lean_dec(v_x_921_);
v_res_924_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_919_, v_x_920_, v_x_1025__boxed_923_, v_x_922_);
lean_dec_ref(v_x_922_);
lean_dec_ref(v_x_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_925_, lean_object* v_keys_926_, lean_object* v_vals_927_, lean_object* v_heq_928_, lean_object* v_i_929_, lean_object* v_k_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_926_, v_vals_927_, v_i_929_, v_k_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_932_, lean_object* v_keys_933_, lean_object* v_vals_934_, lean_object* v_heq_935_, lean_object* v_i_936_, lean_object* v_k_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_932_, v_keys_933_, v_vals_934_, v_heq_935_, v_i_936_, v_k_937_);
lean_dec_ref(v_k_937_);
lean_dec_ref(v_vals_934_);
lean_dec_ref(v_keys_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_939_, lean_object* v_____do__lift_940_){
_start:
{
lean_object* v_charInst_x3f_944_; 
v_charInst_x3f_944_ = lean_ctor_get(v_____do__lift_940_, 5);
lean_inc(v_charInst_x3f_944_);
lean_dec_ref(v_____do__lift_940_);
if (lean_obj_tag(v_charInst_x3f_944_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_956_; 
v_val_945_ = lean_ctor_get(v_charInst_x3f_944_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_charInst_x3f_944_);
if (v_isSharedCheck_956_ == 0)
{
v___x_947_ = v_charInst_x3f_944_;
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v_charInst_x3f_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_snd_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_snd_949_ = lean_ctor_get(v_val_945_, 1);
lean_inc(v_snd_949_);
lean_dec(v_val_945_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_nat_dec_eq(v_snd_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_953_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v_snd_949_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_snd_949_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_apply_2(v_toPure_939_, lean_box(0), v___x_953_);
return v___x_954_;
}
}
else
{
lean_dec(v_snd_949_);
lean_del_object(v___x_947_);
goto v___jp_941_;
}
}
}
else
{
lean_dec(v_charInst_x3f_944_);
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_2(v_toPure_939_, lean_box(0), v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_957_, lean_object* v_inst_958_){
_start:
{
lean_object* v_toApplicative_959_; lean_object* v_toBind_960_; lean_object* v_getRing_961_; lean_object* v_toPure_962_; lean_object* v___f_963_; lean_object* v___x_964_; 
v_toApplicative_959_ = lean_ctor_get(v_inst_957_, 0);
lean_inc_ref(v_toApplicative_959_);
v_toBind_960_ = lean_ctor_get(v_inst_957_, 1);
lean_inc(v_toBind_960_);
lean_dec_ref(v_inst_957_);
v_getRing_961_ = lean_ctor_get(v_inst_958_, 0);
lean_inc(v_getRing_961_);
lean_dec_ref(v_inst_958_);
v_toPure_962_ = lean_ctor_get(v_toApplicative_959_, 1);
lean_inc(v_toPure_962_);
lean_dec_ref(v_toApplicative_959_);
v___f_963_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_963_, 0, v_toPure_962_);
v___x_964_ = lean_apply_4(v_toBind_960_, lean_box(0), lean_box(0), v_getRing_961_, v___f_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_965_, lean_object* v_inst_966_, lean_object* v_inst_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_966_, v_inst_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_969_, lean_object* v_____do__lift_970_){
_start:
{
lean_object* v_charInst_x3f_974_; 
v_charInst_x3f_974_ = lean_ctor_get(v_____do__lift_970_, 5);
lean_inc(v_charInst_x3f_974_);
lean_dec_ref(v_____do__lift_970_);
if (lean_obj_tag(v_charInst_x3f_974_) == 1)
{
lean_object* v_val_975_; lean_object* v_snd_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_val_975_ = lean_ctor_get(v_charInst_x3f_974_, 0);
v_snd_976_ = lean_ctor_get(v_val_975_, 1);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_nat_dec_eq(v_snd_976_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_apply_2(v_toPure_969_, lean_box(0), v_charInst_x3f_974_);
return v___x_979_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_974_, 1);
goto v___jp_971_;
}
}
else
{
lean_dec(v_charInst_x3f_974_);
goto v___jp_971_;
}
v___jp_971_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_box(0);
v___x_973_ = lean_apply_2(v_toPure_969_, lean_box(0), v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_980_, lean_object* v_inst_981_){
_start:
{
lean_object* v_toApplicative_982_; lean_object* v_toBind_983_; lean_object* v_getRing_984_; lean_object* v_toPure_985_; lean_object* v___f_986_; lean_object* v___x_987_; 
v_toApplicative_982_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_982_);
v_toBind_983_ = lean_ctor_get(v_inst_980_, 1);
lean_inc(v_toBind_983_);
lean_dec_ref(v_inst_980_);
v_getRing_984_ = lean_ctor_get(v_inst_981_, 0);
lean_inc(v_getRing_984_);
lean_dec_ref(v_inst_981_);
v_toPure_985_ = lean_ctor_get(v_toApplicative_982_, 1);
lean_inc(v_toPure_985_);
lean_dec_ref(v_toApplicative_982_);
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_986_, 0, v_toPure_985_);
v___x_987_ = lean_apply_4(v_toBind_983_, lean_box(0), lean_box(0), v_getRing_984_, v___f_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_988_, lean_object* v_inst_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_989_, v_inst_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1013_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1013_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_noZeroDivInst_x3f_1009_; lean_object* v___x_1011_; 
v_noZeroDivInst_x3f_1009_ = lean_ctor_get(v_a_1005_, 5);
lean_inc(v_noZeroDivInst_x3f_1009_);
lean_dec(v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v_noZeroDivInst_x3f_1009_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_noZeroDivInst_x3f_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1004_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1004_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1063_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1063_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1063_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_noZeroDivInst_x3f_1052_; 
v_noZeroDivInst_x3f_1052_ = lean_ctor_get(v_a_1048_, 5);
lean_inc(v_noZeroDivInst_x3f_1052_);
lean_dec(v_a_1048_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1052_) == 0)
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = 0;
v___x_1054_ = lean_box(v___x_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1052_, 1);
v___x_1058_ = 1;
v___x_1059_ = lean_box(v___x_1058_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1059_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1047_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1047_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1114_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1114_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1114_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_toRing_1102_; lean_object* v_charInst_x3f_1103_; 
v_toRing_1102_ = lean_ctor_get(v_a_1098_, 0);
lean_inc_ref(v_toRing_1102_);
lean_dec(v_a_1098_);
v_charInst_x3f_1103_ = lean_ctor_get(v_toRing_1102_, 5);
lean_inc(v_charInst_x3f_1103_);
lean_dec_ref(v_toRing_1102_);
if (lean_obj_tag(v_charInst_x3f_1103_) == 0)
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = 0;
v___x_1105_ = lean_box(v___x_1104_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1105_);
v___x_1107_ = v___x_1100_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
else
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_dec_ref_known(v_charInst_x3f_1103_, 1);
v___x_1109_ = 1;
v___x_1110_ = lean_box(v___x_1109_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1110_);
v___x_1112_ = v___x_1100_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1097_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1097_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1135_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1164_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1164_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1164_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_toRing_1156_; lean_object* v_charInst_x3f_1157_; 
v_toRing_1156_ = lean_ctor_get(v_a_1152_, 0);
lean_inc_ref(v_toRing_1156_);
lean_dec(v_a_1152_);
v_charInst_x3f_1157_ = lean_ctor_get(v_toRing_1156_, 5);
lean_inc(v_charInst_x3f_1157_);
lean_dec_ref(v_toRing_1156_);
if (lean_obj_tag(v_charInst_x3f_1157_) == 1)
{
lean_object* v_val_1158_; lean_object* v___x_1160_; 
v_val_1158_ = lean_ctor_get(v_charInst_x3f_1157_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v_charInst_x3f_1157_, 1);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_val_1158_);
v___x_1160_ = v___x_1154_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_val_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_charInst_x3f_1157_);
lean_del_object(v___x_1154_);
v___x_1162_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1163_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1162_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1151_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1151_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1214_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1214_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fieldInst_x3f_1203_; 
v_fieldInst_x3f_1203_ = lean_ctor_get(v_a_1199_, 6);
lean_inc(v_fieldInst_x3f_1203_);
lean_dec(v_a_1199_);
if (lean_obj_tag(v_fieldInst_x3f_1203_) == 0)
{
uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1204_ = 0;
v___x_1205_ = lean_box(v___x_1204_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1205_);
v___x_1207_ = v___x_1201_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_dec_ref_known(v_fieldInst_x3f_1203_, 1);
v___x_1209_ = 1;
v___x_1210_ = lean_box(v___x_1209_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1210_);
v___x_1212_ = v___x_1201_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1198_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1198_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1264_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1264_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1264_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_queue_1253_; 
v_queue_1253_ = lean_ctor_get(v_a_1249_, 11);
lean_inc(v_queue_1253_);
lean_dec(v_a_1249_);
if (lean_obj_tag(v_queue_1253_) == 0)
{
uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
lean_dec_ref_known(v_queue_1253_, 5);
v___x_1254_ = 0;
v___x_1255_ = lean_box(v___x_1254_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1255_);
v___x_1257_ = v___x_1251_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
else
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = 1;
v___x_1260_ = lean_box(v___x_1259_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1260_);
v___x_1262_ = v___x_1251_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1248_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1248_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1286_, lean_object* v_t_1287_){
_start:
{
if (lean_obj_tag(v_t_1287_) == 0)
{
lean_object* v_k_1288_; lean_object* v_v_1289_; lean_object* v_l_1290_; lean_object* v_r_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1945_; 
v_k_1288_ = lean_ctor_get(v_t_1287_, 1);
v_v_1289_ = lean_ctor_get(v_t_1287_, 2);
v_l_1290_ = lean_ctor_get(v_t_1287_, 3);
v_r_1291_ = lean_ctor_get(v_t_1287_, 4);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_t_1287_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v_t_1287_, 0);
lean_dec(v_unused_1946_);
v___x_1293_ = v_t_1287_;
v_isShared_1294_ = v_isSharedCheck_1945_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_r_1291_);
lean_inc(v_l_1290_);
lean_inc(v_v_1289_);
lean_inc(v_k_1288_);
lean_dec(v_t_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1945_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1286_, v_k_1288_);
switch(v___x_1295_)
{
case 0:
{
lean_object* v_impl_1296_; lean_object* v___x_1297_; 
v_impl_1296_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1286_, v_l_1290_);
v___x_1297_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1296_) == 0)
{
if (lean_obj_tag(v_r_1291_) == 0)
{
lean_object* v_size_1298_; lean_object* v_size_1299_; lean_object* v_k_1300_; lean_object* v_v_1301_; lean_object* v_l_1302_; lean_object* v_r_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_size_1298_ = lean_ctor_get(v_impl_1296_, 0);
lean_inc(v_size_1298_);
v_size_1299_ = lean_ctor_get(v_r_1291_, 0);
v_k_1300_ = lean_ctor_get(v_r_1291_, 1);
v_v_1301_ = lean_ctor_get(v_r_1291_, 2);
v_l_1302_ = lean_ctor_get(v_r_1291_, 3);
lean_inc(v_l_1302_);
v_r_1303_ = lean_ctor_get(v_r_1291_, 4);
v___x_1304_ = lean_unsigned_to_nat(3u);
v___x_1305_ = lean_nat_mul(v___x_1304_, v_size_1298_);
v___x_1306_ = lean_nat_dec_lt(v___x_1305_, v_size_1299_);
lean_dec(v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v_l_1302_);
v___x_1307_ = lean_nat_add(v___x_1297_, v_size_1298_);
lean_dec(v_size_1298_);
v___x_1308_ = lean_nat_add(v___x_1307_, v_size_1299_);
lean_dec(v___x_1307_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 3, v_impl_1296_);
lean_ctor_set(v___x_1293_, 0, v___x_1308_);
v___x_1310_ = v___x_1293_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_impl_1296_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_r_1291_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1375_; 
lean_inc(v_r_1303_);
lean_inc(v_v_1301_);
lean_inc(v_k_1300_);
lean_inc(v_size_1299_);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; 
v_unused_1376_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1291_, 2);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1291_, 1);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1380_);
v___x_1313_ = v_r_1291_;
v_isShared_1314_ = v_isSharedCheck_1375_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v_r_1291_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1375_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_size_1315_; lean_object* v_k_1316_; lean_object* v_v_1317_; lean_object* v_l_1318_; lean_object* v_r_1319_; lean_object* v_size_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_size_1315_ = lean_ctor_get(v_l_1302_, 0);
v_k_1316_ = lean_ctor_get(v_l_1302_, 1);
v_v_1317_ = lean_ctor_get(v_l_1302_, 2);
v_l_1318_ = lean_ctor_get(v_l_1302_, 3);
v_r_1319_ = lean_ctor_get(v_l_1302_, 4);
v_size_1320_ = lean_ctor_get(v_r_1303_, 0);
v___x_1321_ = lean_unsigned_to_nat(2u);
v___x_1322_ = lean_nat_mul(v___x_1321_, v_size_1320_);
v___x_1323_ = lean_nat_dec_lt(v_size_1315_, v___x_1322_);
lean_dec(v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_r_1319_);
lean_inc(v_l_1318_);
lean_inc(v_v_1317_);
lean_inc(v_k_1316_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_l_1302_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1352_ = lean_ctor_get(v_l_1302_, 4);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1302_, 3);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1302_, 2);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1302_, 1);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_l_1302_, 0);
lean_dec(v_unused_1356_);
v___x_1325_ = v_l_1302_;
v_isShared_1326_ = v_isSharedCheck_1351_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_l_1302_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1351_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1341_; 
v___x_1327_ = lean_nat_add(v___x_1297_, v_size_1298_);
lean_dec(v_size_1298_);
v___x_1328_ = lean_nat_add(v___x_1327_, v_size_1299_);
lean_dec(v_size_1299_);
if (lean_obj_tag(v_l_1318_) == 0)
{
lean_object* v_size_1349_; 
v_size_1349_ = lean_ctor_get(v_l_1318_, 0);
lean_inc(v_size_1349_);
v___y_1341_ = v_size_1349_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___y_1341_ = v___x_1350_;
goto v___jp_1340_;
}
v___jp_1329_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = lean_nat_add(v___y_1330_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec(v___y_1330_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v_r_1303_);
lean_ctor_set(v___x_1325_, 3, v_r_1319_);
lean_ctor_set(v___x_1325_, 2, v_v_1301_);
lean_ctor_set(v___x_1325_, 1, v_k_1300_);
lean_ctor_set(v___x_1325_, 0, v___x_1333_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1300_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1301_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_r_1319_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1303_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 4, v___x_1335_);
lean_ctor_set(v___x_1313_, 3, v___y_1331_);
lean_ctor_set(v___x_1313_, 2, v_v_1317_);
lean_ctor_set(v___x_1313_, 1, v_k_1316_);
lean_ctor_set(v___x_1313_, 0, v___x_1328_);
v___x_1337_ = v___x_1313_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1316_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1317_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v___y_1331_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
v___jp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_nat_add(v___x_1327_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec(v___x_1327_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_l_1318_);
lean_ctor_set(v___x_1293_, 3, v_impl_1296_);
lean_ctor_set(v___x_1293_, 0, v___x_1342_);
v___x_1344_ = v___x_1293_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_impl_1296_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v_l_1318_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_nat_add(v___x_1297_, v_size_1320_);
if (lean_obj_tag(v_r_1319_) == 0)
{
lean_object* v_size_1346_; 
v_size_1346_ = lean_ctor_get(v_r_1319_, 0);
lean_inc(v_size_1346_);
v___y_1330_ = v___x_1345_;
v___y_1331_ = v___x_1344_;
v___y_1332_ = v_size_1346_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___y_1330_ = v___x_1345_;
v___y_1331_ = v___x_1344_;
v___y_1332_ = v___x_1347_;
goto v___jp_1329_;
}
}
}
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_del_object(v___x_1293_);
v___x_1357_ = lean_nat_add(v___x_1297_, v_size_1298_);
lean_dec(v_size_1298_);
v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1299_);
lean_dec(v_size_1299_);
v___x_1359_ = lean_nat_add(v___x_1357_, v_size_1315_);
lean_dec(v___x_1357_);
lean_inc_ref(v_impl_1296_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 4, v_l_1302_);
lean_ctor_set(v___x_1313_, 3, v_impl_1296_);
lean_ctor_set(v___x_1313_, 2, v_v_1289_);
lean_ctor_set(v___x_1313_, 1, v_k_1288_);
lean_ctor_set(v___x_1313_, 0, v___x_1359_);
v___x_1361_ = v___x_1313_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_impl_1296_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_l_1302_);
v___x_1361_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_isSharedCheck_1368_ = !lean_is_exclusive(v_impl_1296_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1369_ = lean_ctor_get(v_impl_1296_, 4);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_impl_1296_, 3);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_impl_1296_, 2);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_impl_1296_, 1);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_impl_1296_, 0);
lean_dec(v_unused_1373_);
v___x_1363_ = v_impl_1296_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v_impl_1296_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 4, v_r_1303_);
lean_ctor_set(v___x_1363_, 3, v___x_1361_);
lean_ctor_set(v___x_1363_, 2, v_v_1301_);
lean_ctor_set(v___x_1363_, 1, v_k_1300_);
lean_ctor_set(v___x_1363_, 0, v___x_1358_);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1300_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1301_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_r_1303_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v_size_1381_ = lean_ctor_get(v_impl_1296_, 0);
lean_inc(v_size_1381_);
v___x_1382_ = lean_nat_add(v___x_1297_, v_size_1381_);
lean_dec(v_size_1381_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 3, v_impl_1296_);
lean_ctor_set(v___x_1293_, 0, v___x_1382_);
v___x_1384_ = v___x_1293_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_impl_1296_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_r_1291_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
if (lean_obj_tag(v_r_1291_) == 0)
{
lean_object* v_l_1386_; 
v_l_1386_ = lean_ctor_get(v_r_1291_, 3);
lean_inc(v_l_1386_);
if (lean_obj_tag(v_l_1386_) == 0)
{
lean_object* v_r_1387_; 
v_r_1387_ = lean_ctor_get(v_r_1291_, 4);
lean_inc(v_r_1387_);
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1403_; 
v_size_1388_ = lean_ctor_get(v_r_1291_, 0);
v_k_1389_ = lean_ctor_get(v_r_1291_, 1);
v_v_1390_ = lean_ctor_get(v_r_1291_, 2);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1404_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1405_);
v___x_1392_ = v_r_1291_;
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_v_1390_);
lean_inc(v_k_1389_);
lean_inc(v_size_1388_);
lean_dec(v_r_1291_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_size_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v_size_1394_ = lean_ctor_get(v_l_1386_, 0);
v___x_1395_ = lean_nat_add(v___x_1297_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1396_ = lean_nat_add(v___x_1297_, v_size_1394_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1386_);
lean_ctor_set(v___x_1392_, 3, v_impl_1296_);
lean_ctor_set(v___x_1392_, 2, v_v_1289_);
lean_ctor_set(v___x_1392_, 1, v_k_1288_);
lean_ctor_set(v___x_1392_, 0, v___x_1396_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_impl_1296_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_l_1386_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_r_1387_);
lean_ctor_set(v___x_1293_, 3, v___x_1398_);
lean_ctor_set(v___x_1293_, 2, v_v_1390_);
lean_ctor_set(v___x_1293_, 1, v_k_1389_);
lean_ctor_set(v___x_1293_, 0, v___x_1395_);
v___x_1400_ = v___x_1293_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_r_1387_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1430_; 
v_k_1406_ = lean_ctor_get(v_r_1291_, 1);
v_v_1407_ = lean_ctor_get(v_r_1291_, 2);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; 
v_unused_1431_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1433_);
v___x_1409_ = v_r_1291_;
v_isShared_1410_ = v_isSharedCheck_1430_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_v_1407_);
lean_inc(v_k_1406_);
lean_dec(v_r_1291_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1430_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_k_1411_; lean_object* v_v_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1426_; 
v_k_1411_ = lean_ctor_get(v_l_1386_, 1);
v_v_1412_ = lean_ctor_get(v_l_1386_, 2);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_l_1386_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1427_ = lean_ctor_get(v_l_1386_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_l_1386_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_l_1386_, 0);
lean_dec(v_unused_1429_);
v___x_1414_ = v_l_1386_;
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_v_1412_);
lean_inc(v_k_1411_);
lean_dec(v_l_1386_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1426_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_unsigned_to_nat(3u);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_r_1387_);
lean_ctor_set(v___x_1414_, 3, v_r_1387_);
lean_ctor_set(v___x_1414_, 2, v_v_1289_);
lean_ctor_set(v___x_1414_, 1, v_k_1288_);
lean_ctor_set(v___x_1414_, 0, v___x_1297_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_r_1387_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_r_1387_);
v___x_1418_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 3, v_r_1387_);
lean_ctor_set(v___x_1409_, 0, v___x_1297_);
v___x_1420_ = v___x_1409_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_r_1387_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_r_1387_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1420_);
lean_ctor_set(v___x_1293_, 3, v___x_1418_);
lean_ctor_set(v___x_1293_, 2, v_v_1412_);
lean_ctor_set(v___x_1293_, 1, v_k_1411_);
lean_ctor_set(v___x_1293_, 0, v___x_1416_);
v___x_1422_ = v___x_1293_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1411_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1412_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1434_; 
v_r_1434_ = lean_ctor_get(v_r_1291_, 4);
lean_inc(v_r_1434_);
if (lean_obj_tag(v_r_1434_) == 0)
{
lean_object* v_k_1435_; lean_object* v_v_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1447_; 
v_k_1435_ = lean_ctor_get(v_r_1291_, 1);
v_v_1436_ = lean_ctor_get(v_r_1291_, 2);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1448_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1450_);
v___x_1438_ = v_r_1291_;
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_v_1436_);
lean_inc(v_k_1435_);
lean_dec(v_r_1291_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1447_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_unsigned_to_nat(3u);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 4, v_l_1386_);
lean_ctor_set(v___x_1438_, 2, v_v_1289_);
lean_ctor_set(v___x_1438_, 1, v_k_1288_);
lean_ctor_set(v___x_1438_, 0, v___x_1297_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_l_1386_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_l_1386_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_r_1434_);
lean_ctor_set(v___x_1293_, 3, v___x_1442_);
lean_ctor_set(v___x_1293_, 2, v_v_1436_);
lean_ctor_set(v___x_1293_, 1, v_k_1435_);
lean_ctor_set(v___x_1293_, 0, v___x_1440_);
v___x_1444_ = v___x_1293_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1434_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_size_1451_; lean_object* v_k_1452_; lean_object* v_v_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1464_; 
v_size_1451_ = lean_ctor_get(v_r_1291_, 0);
v_k_1452_ = lean_ctor_get(v_r_1291_, 1);
v_v_1453_ = lean_ctor_get(v_r_1291_, 2);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; 
v_unused_1465_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1466_);
v___x_1455_ = v_r_1291_;
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_v_1453_);
lean_inc(v_k_1452_);
lean_inc(v_size_1451_);
lean_dec(v_r_1291_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1464_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 3, v_r_1434_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_size_1451_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1452_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1453_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_r_1434_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_r_1434_);
v___x_1458_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(2u);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1458_);
lean_ctor_set(v___x_1293_, 3, v_r_1434_);
lean_ctor_set(v___x_1293_, 0, v___x_1459_);
v___x_1461_ = v___x_1293_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_r_1434_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v___x_1458_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
else
{
lean_object* v___x_1468_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 3, v_r_1291_);
lean_ctor_set(v___x_1293_, 0, v___x_1297_);
v___x_1468_ = v___x_1293_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_r_1291_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_r_1291_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1293_);
lean_dec(v_v_1289_);
lean_dec(v_k_1288_);
if (lean_obj_tag(v_l_1290_) == 0)
{
if (lean_obj_tag(v_r_1291_) == 0)
{
lean_object* v_size_1470_; lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v_l_1473_; lean_object* v_r_1474_; lean_object* v_size_1475_; lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v_l_1478_; lean_object* v_r_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_size_1470_ = lean_ctor_get(v_l_1290_, 0);
v_k_1471_ = lean_ctor_get(v_l_1290_, 1);
v_v_1472_ = lean_ctor_get(v_l_1290_, 2);
v_l_1473_ = lean_ctor_get(v_l_1290_, 3);
v_r_1474_ = lean_ctor_get(v_l_1290_, 4);
lean_inc(v_r_1474_);
v_size_1475_ = lean_ctor_get(v_r_1291_, 0);
v_k_1476_ = lean_ctor_get(v_r_1291_, 1);
v_v_1477_ = lean_ctor_get(v_r_1291_, 2);
v_l_1478_ = lean_ctor_get(v_r_1291_, 3);
lean_inc(v_l_1478_);
v_r_1479_ = lean_ctor_get(v_r_1291_, 4);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_dec_lt(v_size_1470_, v_size_1475_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1617_; 
lean_inc(v_l_1473_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1618_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_l_1290_, 2);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_l_1290_, 1);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1622_);
v___x_1483_ = v_l_1290_;
v_isShared_1484_ = v_isSharedCheck_1617_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_l_1290_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1617_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v_tree_1486_; 
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1471_, v_v_1472_, v_l_1473_, v_r_1474_);
v_tree_1486_ = lean_ctor_get(v___x_1485_, 2);
lean_inc(v_tree_1486_);
if (lean_obj_tag(v_tree_1486_) == 0)
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v_size_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_k_1487_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_k_1487_);
v_v_1488_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_v_1488_);
lean_dec_ref(v___x_1485_);
v_size_1489_ = lean_ctor_get(v_tree_1486_, 0);
v___x_1490_ = lean_unsigned_to_nat(3u);
v___x_1491_ = lean_nat_mul(v___x_1490_, v_size_1489_);
v___x_1492_ = lean_nat_dec_lt(v___x_1491_, v_size_1475_);
lean_dec(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
lean_dec(v_l_1478_);
v___x_1493_ = lean_nat_add(v___x_1480_, v_size_1489_);
v___x_1494_ = lean_nat_add(v___x_1493_, v_size_1475_);
lean_dec(v___x_1493_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_r_1291_);
lean_ctor_set(v___x_1483_, 3, v_tree_1486_);
lean_ctor_set(v___x_1483_, 2, v_v_1488_);
lean_ctor_set(v___x_1483_, 1, v_k_1487_);
lean_ctor_set(v___x_1483_, 0, v___x_1494_);
v___x_1496_ = v___x_1483_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_tree_1486_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_r_1291_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1552_; 
lean_inc(v_r_1479_);
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
lean_inc(v_size_1475_);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; lean_object* v_unused_1554_; lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1553_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_r_1291_, 2);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_r_1291_, 1);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1557_);
v___x_1499_ = v_r_1291_;
v_isShared_1500_ = v_isSharedCheck_1552_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v_r_1291_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1552_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_size_1501_; lean_object* v_k_1502_; lean_object* v_v_1503_; lean_object* v_l_1504_; lean_object* v_r_1505_; lean_object* v_size_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_size_1501_ = lean_ctor_get(v_l_1478_, 0);
v_k_1502_ = lean_ctor_get(v_l_1478_, 1);
v_v_1503_ = lean_ctor_get(v_l_1478_, 2);
v_l_1504_ = lean_ctor_get(v_l_1478_, 3);
v_r_1505_ = lean_ctor_get(v_l_1478_, 4);
v_size_1506_ = lean_ctor_get(v_r_1479_, 0);
v___x_1507_ = lean_unsigned_to_nat(2u);
v___x_1508_ = lean_nat_mul(v___x_1507_, v_size_1506_);
v___x_1509_ = lean_nat_dec_lt(v_size_1501_, v___x_1508_);
lean_dec(v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1537_; 
lean_inc(v_r_1505_);
lean_inc(v_l_1504_);
lean_inc(v_v_1503_);
lean_inc(v_k_1502_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_l_1478_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; 
v_unused_1538_ = lean_ctor_get(v_l_1478_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_l_1478_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1478_, 2);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_l_1478_, 1);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_l_1478_, 0);
lean_dec(v_unused_1542_);
v___x_1511_ = v_l_1478_;
v_isShared_1512_ = v_isSharedCheck_1537_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_l_1478_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1537_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1527_; 
v___x_1513_ = lean_nat_add(v___x_1480_, v_size_1489_);
v___x_1514_ = lean_nat_add(v___x_1513_, v_size_1475_);
lean_dec(v_size_1475_);
if (lean_obj_tag(v_l_1504_) == 0)
{
lean_object* v_size_1535_; 
v_size_1535_ = lean_ctor_get(v_l_1504_, 0);
lean_inc(v_size_1535_);
v___y_1527_ = v_size_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___y_1527_ = v___x_1536_;
goto v___jp_1526_;
}
v___jp_1515_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_nat_add(v___y_1516_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec(v___y_1516_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 4, v_r_1479_);
lean_ctor_set(v___x_1511_, 3, v_r_1505_);
lean_ctor_set(v___x_1511_, 2, v_v_1477_);
lean_ctor_set(v___x_1511_, 1, v_k_1476_);
lean_ctor_set(v___x_1511_, 0, v___x_1519_);
v___x_1521_ = v___x_1511_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_r_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_r_1479_);
v___x_1521_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v___x_1521_);
lean_ctor_set(v___x_1499_, 3, v___y_1517_);
lean_ctor_set(v___x_1499_, 2, v_v_1503_);
lean_ctor_set(v___x_1499_, 1, v_k_1502_);
lean_ctor_set(v___x_1499_, 0, v___x_1514_);
v___x_1523_ = v___x_1499_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1502_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1503_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v___y_1517_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_nat_add(v___x_1513_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec(v___x_1513_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_l_1504_);
lean_ctor_set(v___x_1483_, 3, v_tree_1486_);
lean_ctor_set(v___x_1483_, 2, v_v_1488_);
lean_ctor_set(v___x_1483_, 1, v_k_1487_);
lean_ctor_set(v___x_1483_, 0, v___x_1528_);
v___x_1530_ = v___x_1483_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_tree_1486_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_l_1504_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_nat_add(v___x_1480_, v_size_1506_);
if (lean_obj_tag(v_r_1505_) == 0)
{
lean_object* v_size_1532_; 
v_size_1532_ = lean_ctor_get(v_r_1505_, 0);
lean_inc(v_size_1532_);
v___y_1516_ = v___x_1531_;
v___y_1517_ = v___x_1530_;
v___y_1518_ = v_size_1532_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
v___y_1516_ = v___x_1531_;
v___y_1517_ = v___x_1530_;
v___y_1518_ = v___x_1533_;
goto v___jp_1515_;
}
}
}
}
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1543_ = lean_nat_add(v___x_1480_, v_size_1489_);
v___x_1544_ = lean_nat_add(v___x_1543_, v_size_1475_);
lean_dec(v_size_1475_);
v___x_1545_ = lean_nat_add(v___x_1543_, v_size_1501_);
lean_dec(v___x_1543_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v_l_1478_);
lean_ctor_set(v___x_1499_, 3, v_tree_1486_);
lean_ctor_set(v___x_1499_, 2, v_v_1488_);
lean_ctor_set(v___x_1499_, 1, v_k_1487_);
lean_ctor_set(v___x_1499_, 0, v___x_1545_);
v___x_1547_ = v___x_1499_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_tree_1486_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v_l_1478_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_r_1479_);
lean_ctor_set(v___x_1483_, 3, v___x_1547_);
lean_ctor_set(v___x_1483_, 2, v_v_1477_);
lean_ctor_set(v___x_1483_, 1, v_k_1476_);
lean_ctor_set(v___x_1483_, 0, v___x_1544_);
v___x_1549_ = v___x_1483_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_r_1479_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
else
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1611_; 
lean_inc(v_r_1479_);
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
lean_inc(v_size_1475_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1612_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1291_, 2);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_r_1291_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1616_);
v___x_1559_ = v_r_1291_;
v_isShared_1560_ = v_isSharedCheck_1611_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_r_1291_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1611_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
if (lean_obj_tag(v_l_1478_) == 0)
{
if (lean_obj_tag(v_r_1479_) == 0)
{
lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v_size_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v_k_1561_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_k_1561_);
v_v_1562_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_v_1562_);
lean_dec_ref(v___x_1485_);
v_size_1563_ = lean_ctor_get(v_l_1478_, 0);
v___x_1564_ = lean_nat_add(v___x_1480_, v_size_1475_);
lean_dec(v_size_1475_);
v___x_1565_ = lean_nat_add(v___x_1480_, v_size_1563_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1478_);
lean_ctor_set(v___x_1559_, 3, v_tree_1486_);
lean_ctor_set(v___x_1559_, 2, v_v_1562_);
lean_ctor_set(v___x_1559_, 1, v_k_1561_);
lean_ctor_set(v___x_1559_, 0, v___x_1565_);
v___x_1567_ = v___x_1559_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_tree_1486_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_l_1478_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_r_1479_);
lean_ctor_set(v___x_1483_, 3, v___x_1567_);
lean_ctor_set(v___x_1483_, 2, v_v_1477_);
lean_ctor_set(v___x_1483_, 1, v_k_1476_);
lean_ctor_set(v___x_1483_, 0, v___x_1564_);
v___x_1569_ = v___x_1483_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_r_1479_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
else
{
lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v_k_1574_; lean_object* v_v_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_size_1475_);
v_k_1572_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_k_1572_);
v_v_1573_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_v_1573_);
lean_dec_ref(v___x_1485_);
v_k_1574_ = lean_ctor_get(v_l_1478_, 1);
v_v_1575_ = lean_ctor_get(v_l_1478_, 2);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_l_1478_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1590_ = lean_ctor_get(v_l_1478_, 4);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1478_, 3);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1478_, 0);
lean_dec(v_unused_1592_);
v___x_1577_ = v_l_1478_;
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_v_1575_);
lean_inc(v_k_1574_);
lean_dec(v_l_1478_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1589_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_unsigned_to_nat(3u);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 4, v_r_1479_);
lean_ctor_set(v___x_1577_, 3, v_r_1479_);
lean_ctor_set(v___x_1577_, 2, v_v_1573_);
lean_ctor_set(v___x_1577_, 1, v_k_1572_);
lean_ctor_set(v___x_1577_, 0, v___x_1480_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_r_1479_);
v___x_1581_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 3, v_r_1479_);
lean_ctor_set(v___x_1559_, 0, v___x_1480_);
v___x_1583_ = v___x_1559_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_r_1479_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1583_);
lean_ctor_set(v___x_1483_, 3, v___x_1581_);
lean_ctor_set(v___x_1483_, 2, v_v_1575_);
lean_ctor_set(v___x_1483_, 1, v_k_1574_);
lean_ctor_set(v___x_1483_, 0, v___x_1579_);
v___x_1585_ = v___x_1483_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1574_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1575_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1479_) == 0)
{
lean_object* v_k_1593_; lean_object* v_v_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v_size_1475_);
v_k_1593_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_k_1593_);
v_v_1594_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_v_1594_);
lean_dec_ref(v___x_1485_);
v___x_1595_ = lean_unsigned_to_nat(3u);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 4, v_l_1478_);
lean_ctor_set(v___x_1559_, 2, v_v_1594_);
lean_ctor_set(v___x_1559_, 1, v_k_1593_);
lean_ctor_set(v___x_1559_, 0, v___x_1480_);
v___x_1597_ = v___x_1559_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1593_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1594_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1478_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_l_1478_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_r_1479_);
lean_ctor_set(v___x_1483_, 3, v___x_1597_);
lean_ctor_set(v___x_1483_, 2, v_v_1477_);
lean_ctor_set(v___x_1483_, 1, v_k_1476_);
lean_ctor_set(v___x_1483_, 0, v___x_1595_);
v___x_1599_ = v___x_1483_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_r_1479_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
else
{
lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v___x_1605_; 
v_k_1602_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_k_1602_);
v_v_1603_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_v_1603_);
lean_dec_ref(v___x_1485_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 3, v_r_1479_);
v___x_1605_ = v___x_1559_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_1475_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1479_);
v___x_1605_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_unsigned_to_nat(2u);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1605_);
lean_ctor_set(v___x_1483_, 3, v_r_1479_);
lean_ctor_set(v___x_1483_, 2, v_v_1603_);
lean_ctor_set(v___x_1483_, 1, v_k_1602_);
lean_ctor_set(v___x_1483_, 0, v___x_1606_);
v___x_1608_ = v___x_1483_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_r_1479_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v___x_1605_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
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
lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1775_; 
lean_inc(v_r_1479_);
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; lean_object* v_unused_1780_; 
v_unused_1776_ = lean_ctor_get(v_r_1291_, 4);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_r_1291_, 3);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_r_1291_, 2);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_r_1291_, 1);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_r_1291_, 0);
lean_dec(v_unused_1780_);
v___x_1624_ = v_r_1291_;
v_isShared_1625_ = v_isSharedCheck_1775_;
goto v_resetjp_1623_;
}
else
{
lean_dec(v_r_1291_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1775_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v_tree_1627_; 
v___x_1626_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1476_, v_v_1477_, v_l_1478_, v_r_1479_);
v_tree_1627_ = lean_ctor_get(v___x_1626_, 2);
lean_inc(v_tree_1627_);
if (lean_obj_tag(v_tree_1627_) == 0)
{
lean_object* v_k_1628_; lean_object* v_v_1629_; lean_object* v_size_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_k_1628_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_k_1628_);
v_v_1629_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_v_1629_);
lean_dec_ref(v___x_1626_);
v_size_1630_ = lean_ctor_get(v_tree_1627_, 0);
v___x_1631_ = lean_unsigned_to_nat(3u);
v___x_1632_ = lean_nat_mul(v___x_1631_, v_size_1630_);
v___x_1633_ = lean_nat_dec_lt(v___x_1632_, v_size_1470_);
lean_dec(v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec(v_r_1474_);
v___x_1634_ = lean_nat_add(v___x_1480_, v_size_1470_);
v___x_1635_ = lean_nat_add(v___x_1634_, v_size_1630_);
lean_dec(v___x_1634_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_tree_1627_);
lean_ctor_set(v___x_1624_, 3, v_l_1290_);
lean_ctor_set(v___x_1624_, 2, v_v_1629_);
lean_ctor_set(v___x_1624_, 1, v_k_1628_);
lean_ctor_set(v___x_1624_, 0, v___x_1635_);
v___x_1637_ = v___x_1624_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_tree_1627_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1704_; 
lean_inc(v_l_1473_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_inc(v_size_1470_);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1705_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_l_1290_, 2);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_l_1290_, 1);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1709_);
v___x_1640_ = v_l_1290_;
v_isShared_1641_ = v_isSharedCheck_1704_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_l_1290_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1704_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_size_1642_; lean_object* v_size_1643_; lean_object* v_k_1644_; lean_object* v_v_1645_; lean_object* v_l_1646_; lean_object* v_r_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_size_1642_ = lean_ctor_get(v_l_1473_, 0);
v_size_1643_ = lean_ctor_get(v_r_1474_, 0);
v_k_1644_ = lean_ctor_get(v_r_1474_, 1);
v_v_1645_ = lean_ctor_get(v_r_1474_, 2);
v_l_1646_ = lean_ctor_get(v_r_1474_, 3);
v_r_1647_ = lean_ctor_get(v_r_1474_, 4);
v___x_1648_ = lean_unsigned_to_nat(2u);
v___x_1649_ = lean_nat_mul(v___x_1648_, v_size_1642_);
v___x_1650_ = lean_nat_dec_lt(v_size_1643_, v___x_1649_);
lean_dec(v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1688_; 
lean_inc(v_r_1647_);
lean_inc(v_l_1646_);
lean_inc(v_v_1645_);
lean_inc(v_k_1644_);
lean_del_object(v___x_1640_);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_r_1474_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1689_ = lean_ctor_get(v_r_1474_, 4);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_r_1474_, 3);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_r_1474_, 2);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_r_1474_, 1);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_r_1474_, 0);
lean_dec(v_unused_1693_);
v___x_1652_ = v_r_1474_;
v_isShared_1653_ = v_isSharedCheck_1688_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v_r_1474_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1688_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___x_1676_; lean_object* v___y_1678_; 
v___x_1654_ = lean_nat_add(v___x_1480_, v_size_1470_);
lean_dec(v_size_1470_);
v___x_1655_ = lean_nat_add(v___x_1654_, v_size_1630_);
lean_dec(v___x_1654_);
v___x_1676_ = lean_nat_add(v___x_1480_, v_size_1642_);
if (lean_obj_tag(v_l_1646_) == 0)
{
lean_object* v_size_1686_; 
v_size_1686_ = lean_ctor_get(v_l_1646_, 0);
lean_inc(v_size_1686_);
v___y_1678_ = v_size_1686_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v___y_1678_ = v___x_1687_;
goto v___jp_1677_;
}
v___jp_1656_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_nat_add(v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec(v___y_1658_);
lean_inc_ref(v_tree_1627_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 4, v_tree_1627_);
lean_ctor_set(v___x_1652_, 3, v_r_1647_);
lean_ctor_set(v___x_1652_, 2, v_v_1629_);
lean_ctor_set(v___x_1652_, 1, v_k_1628_);
lean_ctor_set(v___x_1652_, 0, v___x_1660_);
v___x_1662_ = v___x_1652_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_r_1647_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_tree_1627_);
v___x_1662_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_isSharedCheck_1669_ = !lean_is_exclusive(v_tree_1627_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; 
v_unused_1670_ = lean_ctor_get(v_tree_1627_, 4);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_tree_1627_, 3);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_tree_1627_, 2);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_tree_1627_, 1);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_tree_1627_, 0);
lean_dec(v_unused_1674_);
v___x_1664_ = v_tree_1627_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_dec(v_tree_1627_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 4, v___x_1662_);
lean_ctor_set(v___x_1664_, 3, v___y_1657_);
lean_ctor_set(v___x_1664_, 2, v_v_1645_);
lean_ctor_set(v___x_1664_, 1, v_k_1644_);
lean_ctor_set(v___x_1664_, 0, v___x_1655_);
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1644_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1645_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v___y_1657_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v___x_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
v___jp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_nat_add(v___x_1676_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec(v___x_1676_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_l_1646_);
lean_ctor_set(v___x_1624_, 3, v_l_1473_);
lean_ctor_set(v___x_1624_, 2, v_v_1472_);
lean_ctor_set(v___x_1624_, 1, v_k_1471_);
lean_ctor_set(v___x_1624_, 0, v___x_1679_);
v___x_1681_ = v___x_1624_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_l_1646_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_nat_add(v___x_1480_, v_size_1630_);
if (lean_obj_tag(v_r_1647_) == 0)
{
lean_object* v_size_1683_; 
v_size_1683_ = lean_ctor_get(v_r_1647_, 0);
lean_inc(v_size_1683_);
v___y_1657_ = v___x_1681_;
v___y_1658_ = v___x_1682_;
v___y_1659_ = v_size_1683_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___y_1657_ = v___x_1681_;
v___y_1658_ = v___x_1682_;
v___y_1659_ = v___x_1684_;
goto v___jp_1656_;
}
}
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1694_ = lean_nat_add(v___x_1480_, v_size_1470_);
lean_dec(v_size_1470_);
v___x_1695_ = lean_nat_add(v___x_1694_, v_size_1630_);
lean_dec(v___x_1694_);
v___x_1696_ = lean_nat_add(v___x_1480_, v_size_1630_);
v___x_1697_ = lean_nat_add(v___x_1696_, v_size_1643_);
lean_dec(v___x_1696_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_tree_1627_);
lean_ctor_set(v___x_1624_, 3, v_r_1474_);
lean_ctor_set(v___x_1624_, 2, v_v_1629_);
lean_ctor_set(v___x_1624_, 1, v_k_1628_);
lean_ctor_set(v___x_1624_, 0, v___x_1697_);
v___x_1699_ = v___x_1624_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_r_1474_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_tree_1627_);
v___x_1699_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 4, v___x_1699_);
lean_ctor_set(v___x_1640_, 0, v___x_1695_);
v___x_1701_ = v___x_1640_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1473_) == 0)
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1733_; 
lean_inc_ref(v_l_1473_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_inc(v_size_1470_);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; lean_object* v_unused_1735_; lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1734_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_l_1290_, 2);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_l_1290_, 1);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1738_);
v___x_1711_ = v_l_1290_;
v_isShared_1712_ = v_isSharedCheck_1733_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v_l_1290_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1733_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
if (lean_obj_tag(v_r_1474_) == 0)
{
lean_object* v_k_1713_; lean_object* v_v_1714_; lean_object* v_size_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v_k_1713_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_k_1713_);
v_v_1714_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_v_1714_);
lean_dec_ref(v___x_1626_);
v_size_1715_ = lean_ctor_get(v_r_1474_, 0);
v___x_1716_ = lean_nat_add(v___x_1480_, v_size_1470_);
lean_dec(v_size_1470_);
v___x_1717_ = lean_nat_add(v___x_1480_, v_size_1715_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_tree_1627_);
lean_ctor_set(v___x_1624_, 3, v_r_1474_);
lean_ctor_set(v___x_1624_, 2, v_v_1714_);
lean_ctor_set(v___x_1624_, 1, v_k_1713_);
lean_ctor_set(v___x_1624_, 0, v___x_1717_);
v___x_1719_ = v___x_1624_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1713_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1714_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_r_1474_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_tree_1627_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v___x_1719_);
lean_ctor_set(v___x_1711_, 0, v___x_1716_);
v___x_1721_ = v___x_1711_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_k_1724_; lean_object* v_v_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec(v_size_1470_);
v_k_1724_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_k_1724_);
v_v_1725_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_v_1725_);
lean_dec_ref(v___x_1626_);
v___x_1726_ = lean_unsigned_to_nat(3u);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_r_1474_);
lean_ctor_set(v___x_1624_, 3, v_r_1474_);
lean_ctor_set(v___x_1624_, 2, v_v_1725_);
lean_ctor_set(v___x_1624_, 1, v_k_1724_);
lean_ctor_set(v___x_1624_, 0, v___x_1480_);
v___x_1728_ = v___x_1624_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_r_1474_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_r_1474_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1730_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 4, v___x_1728_);
lean_ctor_set(v___x_1711_, 0, v___x_1726_);
v___x_1730_ = v___x_1711_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1474_) == 0)
{
lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1763_; 
lean_inc(v_l_1473_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; lean_object* v_unused_1767_; lean_object* v_unused_1768_; 
v_unused_1764_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1290_, 2);
lean_dec(v_unused_1766_);
v_unused_1767_ = lean_ctor_get(v_l_1290_, 1);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1768_);
v___x_1740_ = v_l_1290_;
v_isShared_1741_ = v_isSharedCheck_1763_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v_l_1290_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1763_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_k_1742_; lean_object* v_v_1743_; lean_object* v_k_1744_; lean_object* v_v_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1759_; 
v_k_1742_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_k_1742_);
v_v_1743_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_v_1743_);
lean_dec_ref(v___x_1626_);
v_k_1744_ = lean_ctor_get(v_r_1474_, 1);
v_v_1745_ = lean_ctor_get(v_r_1474_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_r_1474_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1760_ = lean_ctor_get(v_r_1474_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_r_1474_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_r_1474_, 0);
lean_dec(v_unused_1762_);
v___x_1747_ = v_r_1474_;
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_v_1745_);
lean_inc(v_k_1744_);
lean_dec(v_r_1474_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_unsigned_to_nat(3u);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v_l_1473_);
lean_ctor_set(v___x_1747_, 3, v_l_1473_);
lean_ctor_set(v___x_1747_, 2, v_v_1472_);
lean_ctor_set(v___x_1747_, 1, v_k_1471_);
lean_ctor_set(v___x_1747_, 0, v___x_1480_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_l_1473_);
v___x_1751_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_l_1473_);
lean_ctor_set(v___x_1624_, 3, v_l_1473_);
lean_ctor_set(v___x_1624_, 2, v_v_1743_);
lean_ctor_set(v___x_1624_, 1, v_k_1742_);
lean_ctor_set(v___x_1624_, 0, v___x_1480_);
v___x_1753_ = v___x_1624_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_k_1742_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_v_1743_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_l_1473_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v_l_1473_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v___x_1753_);
lean_ctor_set(v___x_1740_, 3, v___x_1751_);
lean_ctor_set(v___x_1740_, 2, v_v_1745_);
lean_ctor_set(v___x_1740_, 1, v_k_1744_);
lean_ctor_set(v___x_1740_, 0, v___x_1749_);
v___x_1755_ = v___x_1740_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1744_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1745_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v___x_1753_);
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
}
else
{
lean_object* v_k_1769_; lean_object* v_v_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v_k_1769_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_k_1769_);
v_v_1770_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_v_1770_);
lean_dec_ref(v___x_1626_);
v___x_1771_ = lean_unsigned_to_nat(2u);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 4, v_r_1474_);
lean_ctor_set(v___x_1624_, 3, v_l_1290_);
lean_ctor_set(v___x_1624_, 2, v_v_1770_);
lean_ctor_set(v___x_1624_, 1, v_k_1769_);
lean_ctor_set(v___x_1624_, 0, v___x_1771_);
v___x_1773_ = v___x_1624_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_k_1769_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_v_1770_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v_r_1474_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
}
else
{
return v_l_1290_;
}
}
else
{
return v_r_1291_;
}
}
default: 
{
lean_object* v_impl_1781_; lean_object* v___x_1782_; 
v_impl_1781_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1286_, v_r_1291_);
v___x_1782_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1781_) == 0)
{
if (lean_obj_tag(v_l_1290_) == 0)
{
lean_object* v_size_1783_; lean_object* v_size_1784_; lean_object* v_k_1785_; lean_object* v_v_1786_; lean_object* v_l_1787_; lean_object* v_r_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_size_1783_ = lean_ctor_get(v_impl_1781_, 0);
lean_inc(v_size_1783_);
v_size_1784_ = lean_ctor_get(v_l_1290_, 0);
v_k_1785_ = lean_ctor_get(v_l_1290_, 1);
v_v_1786_ = lean_ctor_get(v_l_1290_, 2);
v_l_1787_ = lean_ctor_get(v_l_1290_, 3);
v_r_1788_ = lean_ctor_get(v_l_1290_, 4);
lean_inc(v_r_1788_);
v___x_1789_ = lean_unsigned_to_nat(3u);
v___x_1790_ = lean_nat_mul(v___x_1789_, v_size_1783_);
v___x_1791_ = lean_nat_dec_lt(v___x_1790_, v_size_1784_);
lean_dec(v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec(v_r_1788_);
v___x_1792_ = lean_nat_add(v___x_1782_, v_size_1784_);
v___x_1793_ = lean_nat_add(v___x_1792_, v_size_1783_);
lean_dec(v_size_1783_);
lean_dec(v___x_1792_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_impl_1781_);
lean_ctor_set(v___x_1293_, 0, v___x_1793_);
v___x_1795_ = v___x_1293_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_impl_1781_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
else
{
lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1862_; 
lean_inc(v_l_1787_);
lean_inc(v_v_1786_);
lean_inc(v_k_1785_);
lean_inc(v_size_1784_);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; 
v_unused_1863_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_l_1290_, 2);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_l_1290_, 1);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1867_);
v___x_1798_ = v_l_1290_;
v_isShared_1799_ = v_isSharedCheck_1862_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v_l_1290_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1862_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_size_1800_; lean_object* v_size_1801_; lean_object* v_k_1802_; lean_object* v_v_1803_; lean_object* v_l_1804_; lean_object* v_r_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_size_1800_ = lean_ctor_get(v_l_1787_, 0);
v_size_1801_ = lean_ctor_get(v_r_1788_, 0);
v_k_1802_ = lean_ctor_get(v_r_1788_, 1);
v_v_1803_ = lean_ctor_get(v_r_1788_, 2);
v_l_1804_ = lean_ctor_get(v_r_1788_, 3);
v_r_1805_ = lean_ctor_get(v_r_1788_, 4);
v___x_1806_ = lean_unsigned_to_nat(2u);
v___x_1807_ = lean_nat_mul(v___x_1806_, v_size_1800_);
v___x_1808_ = lean_nat_dec_lt(v_size_1801_, v___x_1807_);
lean_dec(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1837_; 
lean_inc(v_r_1805_);
lean_inc(v_l_1804_);
lean_inc(v_v_1803_);
lean_inc(v_k_1802_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_r_1788_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1838_ = lean_ctor_get(v_r_1788_, 4);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_r_1788_, 3);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1788_, 2);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_r_1788_, 1);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_r_1788_, 0);
lean_dec(v_unused_1842_);
v___x_1810_ = v_r_1788_;
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v_r_1788_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___x_1825_; lean_object* v___y_1827_; 
v___x_1812_ = lean_nat_add(v___x_1782_, v_size_1784_);
lean_dec(v_size_1784_);
v___x_1813_ = lean_nat_add(v___x_1812_, v_size_1783_);
lean_dec(v___x_1812_);
v___x_1825_ = lean_nat_add(v___x_1782_, v_size_1800_);
if (lean_obj_tag(v_l_1804_) == 0)
{
lean_object* v_size_1835_; 
v_size_1835_ = lean_ctor_get(v_l_1804_, 0);
lean_inc(v_size_1835_);
v___y_1827_ = v_size_1835_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___y_1827_ = v___x_1836_;
goto v___jp_1826_;
}
v___jp_1814_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_nat_add(v___y_1815_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec(v___y_1815_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_impl_1781_);
lean_ctor_set(v___x_1810_, 3, v_r_1805_);
lean_ctor_set(v___x_1810_, 2, v_v_1289_);
lean_ctor_set(v___x_1810_, 1, v_k_1288_);
lean_ctor_set(v___x_1810_, 0, v___x_1818_);
v___x_1820_ = v___x_1810_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_r_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_impl_1781_);
v___x_1820_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 4, v___x_1820_);
lean_ctor_set(v___x_1798_, 3, v___y_1816_);
lean_ctor_set(v___x_1798_, 2, v_v_1803_);
lean_ctor_set(v___x_1798_, 1, v_k_1802_);
lean_ctor_set(v___x_1798_, 0, v___x_1813_);
v___x_1822_ = v___x_1798_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_k_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_v_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v___y_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
v___jp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_nat_add(v___x_1825_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec(v___x_1825_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_l_1804_);
lean_ctor_set(v___x_1293_, 3, v_l_1787_);
lean_ctor_set(v___x_1293_, 2, v_v_1786_);
lean_ctor_set(v___x_1293_, 1, v_k_1785_);
lean_ctor_set(v___x_1293_, 0, v___x_1828_);
v___x_1830_ = v___x_1293_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_k_1785_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_v_1786_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_l_1787_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_l_1804_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_nat_add(v___x_1782_, v_size_1783_);
lean_dec(v_size_1783_);
if (lean_obj_tag(v_r_1805_) == 0)
{
lean_object* v_size_1832_; 
v_size_1832_ = lean_ctor_get(v_r_1805_, 0);
lean_inc(v_size_1832_);
v___y_1815_ = v___x_1831_;
v___y_1816_ = v___x_1830_;
v___y_1817_ = v_size_1832_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___y_1815_ = v___x_1831_;
v___y_1816_ = v___x_1830_;
v___y_1817_ = v___x_1833_;
goto v___jp_1814_;
}
}
}
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
lean_del_object(v___x_1293_);
v___x_1843_ = lean_nat_add(v___x_1782_, v_size_1784_);
lean_dec(v_size_1784_);
v___x_1844_ = lean_nat_add(v___x_1843_, v_size_1783_);
lean_dec(v___x_1843_);
v___x_1845_ = lean_nat_add(v___x_1782_, v_size_1783_);
lean_dec(v_size_1783_);
v___x_1846_ = lean_nat_add(v___x_1845_, v_size_1801_);
lean_dec(v___x_1845_);
lean_inc_ref(v_impl_1781_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 4, v_impl_1781_);
lean_ctor_set(v___x_1798_, 3, v_r_1788_);
lean_ctor_set(v___x_1798_, 2, v_v_1289_);
lean_ctor_set(v___x_1798_, 1, v_k_1288_);
lean_ctor_set(v___x_1798_, 0, v___x_1846_);
v___x_1848_ = v___x_1798_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_r_1788_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_impl_1781_);
v___x_1848_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
v_isSharedCheck_1855_ = !lean_is_exclusive(v_impl_1781_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1856_ = lean_ctor_get(v_impl_1781_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_impl_1781_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_impl_1781_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_impl_1781_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_impl_1781_, 0);
lean_dec(v_unused_1860_);
v___x_1850_ = v_impl_1781_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_impl_1781_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 4, v___x_1848_);
lean_ctor_set(v___x_1850_, 3, v_l_1787_);
lean_ctor_set(v___x_1850_, 2, v_v_1786_);
lean_ctor_set(v___x_1850_, 1, v_k_1785_);
lean_ctor_set(v___x_1850_, 0, v___x_1844_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_k_1785_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_v_1786_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_l_1787_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v___x_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v_size_1868_ = lean_ctor_get(v_impl_1781_, 0);
lean_inc(v_size_1868_);
v___x_1869_ = lean_nat_add(v___x_1782_, v_size_1868_);
lean_dec(v_size_1868_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_impl_1781_);
lean_ctor_set(v___x_1293_, 0, v___x_1869_);
v___x_1871_ = v___x_1293_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_impl_1781_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
if (lean_obj_tag(v_l_1290_) == 0)
{
lean_object* v_l_1873_; 
v_l_1873_ = lean_ctor_get(v_l_1290_, 3);
if (lean_obj_tag(v_l_1873_) == 0)
{
lean_object* v_r_1874_; 
lean_inc_ref(v_l_1873_);
v_r_1874_ = lean_ctor_get(v_l_1290_, 4);
lean_inc(v_r_1874_);
if (lean_obj_tag(v_r_1874_) == 0)
{
lean_object* v_size_1875_; lean_object* v_k_1876_; lean_object* v_v_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1890_; 
v_size_1875_ = lean_ctor_get(v_l_1290_, 0);
v_k_1876_ = lean_ctor_get(v_l_1290_, 1);
v_v_1877_ = lean_ctor_get(v_l_1290_, 2);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; lean_object* v_unused_1892_; 
v_unused_1891_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1892_);
v___x_1879_ = v_l_1290_;
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_v_1877_);
lean_inc(v_k_1876_);
lean_inc(v_size_1875_);
lean_dec(v_l_1290_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_size_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v_size_1881_ = lean_ctor_get(v_r_1874_, 0);
v___x_1882_ = lean_nat_add(v___x_1782_, v_size_1875_);
lean_dec(v_size_1875_);
v___x_1883_ = lean_nat_add(v___x_1782_, v_size_1881_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v_impl_1781_);
lean_ctor_set(v___x_1879_, 3, v_r_1874_);
lean_ctor_set(v___x_1879_, 2, v_v_1289_);
lean_ctor_set(v___x_1879_, 1, v_k_1288_);
lean_ctor_set(v___x_1879_, 0, v___x_1883_);
v___x_1885_ = v___x_1879_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_r_1874_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_impl_1781_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1885_);
lean_ctor_set(v___x_1293_, 3, v_l_1873_);
lean_ctor_set(v___x_1293_, 2, v_v_1877_);
lean_ctor_set(v___x_1293_, 1, v_k_1876_);
lean_ctor_set(v___x_1293_, 0, v___x_1882_);
v___x_1887_ = v___x_1293_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_k_1876_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_v_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_l_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_k_1893_; lean_object* v_v_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1905_; 
v_k_1893_ = lean_ctor_get(v_l_1290_, 1);
v_v_1894_ = lean_ctor_get(v_l_1290_, 2);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; 
v_unused_1906_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1908_);
v___x_1896_ = v_l_1290_;
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_v_1894_);
lean_inc(v_k_1893_);
lean_dec(v_l_1290_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_unsigned_to_nat(3u);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 3, v_r_1874_);
lean_ctor_set(v___x_1896_, 2, v_v_1289_);
lean_ctor_set(v___x_1896_, 1, v_k_1288_);
lean_ctor_set(v___x_1896_, 0, v___x_1782_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_r_1874_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v_r_1874_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1900_);
lean_ctor_set(v___x_1293_, 3, v_l_1873_);
lean_ctor_set(v___x_1293_, 2, v_v_1894_);
lean_ctor_set(v___x_1293_, 1, v_k_1893_);
lean_ctor_set(v___x_1293_, 0, v___x_1898_);
v___x_1902_ = v___x_1293_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1893_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1894_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_l_1873_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v_r_1909_; 
v_r_1909_ = lean_ctor_get(v_l_1290_, 4);
lean_inc(v_r_1909_);
if (lean_obj_tag(v_r_1909_) == 0)
{
lean_object* v_k_1910_; lean_object* v_v_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1934_; 
lean_inc(v_l_1873_);
v_k_1910_ = lean_ctor_get(v_l_1290_, 1);
v_v_1911_ = lean_ctor_get(v_l_1290_, 2);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_l_1290_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1935_ = lean_ctor_get(v_l_1290_, 4);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_l_1290_, 3);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_l_1290_, 0);
lean_dec(v_unused_1937_);
v___x_1913_ = v_l_1290_;
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_v_1911_);
lean_inc(v_k_1910_);
lean_dec(v_l_1290_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1930_; 
v_k_1915_ = lean_ctor_get(v_r_1909_, 1);
v_v_1916_ = lean_ctor_get(v_r_1909_, 2);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_r_1909_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; lean_object* v_unused_1932_; lean_object* v_unused_1933_; 
v_unused_1931_ = lean_ctor_get(v_r_1909_, 4);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_r_1909_, 3);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_r_1909_, 0);
lean_dec(v_unused_1933_);
v___x_1918_ = v_r_1909_;
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_v_1916_);
lean_inc(v_k_1915_);
lean_dec(v_r_1909_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_unsigned_to_nat(3u);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 4, v_l_1873_);
lean_ctor_set(v___x_1918_, 3, v_l_1873_);
lean_ctor_set(v___x_1918_, 2, v_v_1911_);
lean_ctor_set(v___x_1918_, 1, v_k_1910_);
lean_ctor_set(v___x_1918_, 0, v___x_1782_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_k_1910_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_v_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_l_1873_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_l_1873_);
v___x_1922_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 4, v_l_1873_);
lean_ctor_set(v___x_1913_, 2, v_v_1289_);
lean_ctor_set(v___x_1913_, 1, v_k_1288_);
lean_ctor_set(v___x_1913_, 0, v___x_1782_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_l_1873_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_l_1873_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1924_);
lean_ctor_set(v___x_1293_, 3, v___x_1922_);
lean_ctor_set(v___x_1293_, 2, v_v_1916_);
lean_ctor_set(v___x_1293_, 1, v_k_1915_);
lean_ctor_set(v___x_1293_, 0, v___x_1920_);
v___x_1926_ = v___x_1293_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1915_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1916_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(2u);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_r_1909_);
lean_ctor_set(v___x_1293_, 0, v___x_1938_);
v___x_1940_ = v___x_1293_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_r_1909_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v___x_1943_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v_l_1290_);
lean_ctor_set(v___x_1293_, 0, v___x_1782_);
v___x_1943_ = v___x_1293_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_k_1288_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_v_1289_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_l_1290_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_l_1290_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
}
else
{
return v_t_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1947_, lean_object* v_t_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1947_, v_t_1948_);
lean_dec_ref(v_k_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1950_, lean_object* v_s_1951_){
_start:
{
lean_object* v_toRing_1952_; lean_object* v_invFn_x3f_1953_; lean_object* v_semiringId_x3f_1954_; lean_object* v_commSemiringInst_1955_; lean_object* v_commRingInst_1956_; lean_object* v_noZeroDivInst_x3f_1957_; lean_object* v_fieldInst_x3f_1958_; lean_object* v_powIdentityInst_x3f_1959_; lean_object* v_denoteEntries_1960_; lean_object* v_nextId_1961_; lean_object* v_steps_1962_; lean_object* v_queue_1963_; lean_object* v_basis_1964_; lean_object* v_diseqs_1965_; uint8_t v_recheck_1966_; lean_object* v_invSet_1967_; lean_object* v_powIdentityVarCount_1968_; lean_object* v_numEq0_x3f_1969_; uint8_t v_numEq0Updated_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_toRing_1952_ = lean_ctor_get(v_s_1951_, 0);
v_invFn_x3f_1953_ = lean_ctor_get(v_s_1951_, 1);
v_semiringId_x3f_1954_ = lean_ctor_get(v_s_1951_, 2);
v_commSemiringInst_1955_ = lean_ctor_get(v_s_1951_, 3);
v_commRingInst_1956_ = lean_ctor_get(v_s_1951_, 4);
v_noZeroDivInst_x3f_1957_ = lean_ctor_get(v_s_1951_, 5);
v_fieldInst_x3f_1958_ = lean_ctor_get(v_s_1951_, 6);
v_powIdentityInst_x3f_1959_ = lean_ctor_get(v_s_1951_, 7);
v_denoteEntries_1960_ = lean_ctor_get(v_s_1951_, 8);
v_nextId_1961_ = lean_ctor_get(v_s_1951_, 9);
v_steps_1962_ = lean_ctor_get(v_s_1951_, 10);
v_queue_1963_ = lean_ctor_get(v_s_1951_, 11);
v_basis_1964_ = lean_ctor_get(v_s_1951_, 12);
v_diseqs_1965_ = lean_ctor_get(v_s_1951_, 13);
v_recheck_1966_ = lean_ctor_get_uint8(v_s_1951_, sizeof(void*)*17);
v_invSet_1967_ = lean_ctor_get(v_s_1951_, 14);
v_powIdentityVarCount_1968_ = lean_ctor_get(v_s_1951_, 15);
v_numEq0_x3f_1969_ = lean_ctor_get(v_s_1951_, 16);
v_numEq0Updated_1970_ = lean_ctor_get_uint8(v_s_1951_, sizeof(void*)*17 + 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_s_1951_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1972_ = v_s_1951_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_numEq0_x3f_1969_);
lean_inc(v_powIdentityVarCount_1968_);
lean_inc(v_invSet_1967_);
lean_inc(v_diseqs_1965_);
lean_inc(v_basis_1964_);
lean_inc(v_queue_1963_);
lean_inc(v_steps_1962_);
lean_inc(v_nextId_1961_);
lean_inc(v_denoteEntries_1960_);
lean_inc(v_powIdentityInst_x3f_1959_);
lean_inc(v_fieldInst_x3f_1958_);
lean_inc(v_noZeroDivInst_x3f_1957_);
lean_inc(v_commRingInst_1956_);
lean_inc(v_commSemiringInst_1955_);
lean_inc(v_semiringId_x3f_1954_);
lean_inc(v_invFn_x3f_1953_);
lean_inc(v_toRing_1952_);
lean_dec(v_s_1951_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1950_, v_queue_1963_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 11, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_toRing_1952_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_invFn_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_semiringId_x3f_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_commSemiringInst_1955_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_commRingInst_1956_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_noZeroDivInst_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_fieldInst_x3f_1958_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_powIdentityInst_x3f_1959_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_denoteEntries_1960_);
lean_ctor_set(v_reuseFailAlloc_1977_, 9, v_nextId_1961_);
lean_ctor_set(v_reuseFailAlloc_1977_, 10, v_steps_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 11, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1977_, 12, v_basis_1964_);
lean_ctor_set(v_reuseFailAlloc_1977_, 13, v_diseqs_1965_);
lean_ctor_set(v_reuseFailAlloc_1977_, 14, v_invSet_1967_);
lean_ctor_set(v_reuseFailAlloc_1977_, 15, v_powIdentityVarCount_1968_);
lean_ctor_set(v_reuseFailAlloc_1977_, 16, v_numEq0_x3f_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*17, v_recheck_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*17 + 1, v_numEq0Updated_1970_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1979_, lean_object* v_s_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1979_, v_s_1980_);
lean_dec_ref(v_val_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2034_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2034_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2034_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_queue_1999_; lean_object* v___x_2000_; 
v_queue_1999_ = lean_ctor_get(v_a_1995_, 11);
lean_inc(v_queue_1999_);
lean_dec(v_a_1995_);
v___x_2000_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1999_);
lean_dec(v_queue_1999_);
if (lean_obj_tag(v___x_2000_) == 1)
{
lean_object* v_val_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; 
lean_del_object(v___x_1997_);
v_val_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_val_2001_);
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2002_, 0, v_val_2001_);
v___x_2003_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2002_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec_ref_known(v___x_2003_, 1);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2004_, v_a_1983_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2013_);
v___x_2007_ = v___x_2005_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___x_2005_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2000_);
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2000_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref_known(v___x_2000_, 1);
v_a_2014_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2005_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2005_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref_known(v___x_2000_, 1);
v_a_2022_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2003_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2003_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v___x_2000_);
v___x_2030_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2030_);
v___x_2032_ = v___x_1997_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1994_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1994_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2056_, lean_object* v_k_2057_, lean_object* v_t_2058_, lean_object* v_h_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2057_, v_t_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2061_, lean_object* v_k_2062_, lean_object* v_t_2063_, lean_object* v_h_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2061_, v_k_2062_, v_t_2063_, v_h_2064_);
lean_dec_ref(v_k_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v_ks_2070_; lean_object* v_vs_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2097_; 
v_ks_2070_ = lean_ctor_get(v_x_2066_, 0);
v_vs_2071_ = lean_ctor_get(v_x_2066_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_x_2066_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2073_ = v_x_2066_;
v_isShared_2074_ = v_isSharedCheck_2097_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_vs_2071_);
lean_inc(v_ks_2070_);
lean_dec(v_x_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2097_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_array_get_size(v_ks_2070_);
v___x_2076_ = lean_nat_dec_lt(v_x_2067_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec(v_x_2067_);
v___x_2077_ = lean_array_push(v_ks_2070_, v_x_2068_);
v___x_2078_ = lean_array_push(v_vs_2071_, v_x_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2078_);
lean_ctor_set(v___x_2073_, 0, v___x_2077_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
else
{
lean_object* v_k_x27_2082_; size_t v___x_2083_; size_t v___x_2084_; uint8_t v___x_2085_; 
v_k_x27_2082_ = lean_array_fget_borrowed(v_ks_2070_, v_x_2067_);
v___x_2083_ = lean_ptr_addr(v_x_2068_);
v___x_2084_ = lean_ptr_addr(v_k_x27_2082_);
v___x_2085_ = lean_usize_dec_eq(v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2087_; 
if (v_isShared_2074_ == 0)
{
v___x_2087_ = v___x_2073_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_ks_2070_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_vs_2071_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_x_2067_, v___x_2088_);
lean_dec(v_x_2067_);
v_x_2066_ = v___x_2087_;
v_x_2067_ = v___x_2089_;
goto _start;
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2092_ = lean_array_fset(v_ks_2070_, v_x_2067_, v_x_2068_);
v___x_2093_ = lean_array_fset(v_vs_2071_, v_x_2067_, v_x_2069_);
lean_dec(v_x_2067_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2093_);
lean_ctor_set(v___x_2073_, 0, v___x_2092_);
v___x_2095_ = v___x_2073_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___x_2093_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2098_, lean_object* v_k_2099_, lean_object* v_v_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2098_, v___x_2101_, v_k_2099_, v_v_2100_);
return v___x_2102_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2104_, size_t v_x_2105_, size_t v_x_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
lean_object* v_es_2109_; size_t v___x_2110_; size_t v___x_2111_; lean_object* v_j_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_es_2109_ = lean_ctor_get(v_x_2104_, 0);
v___x_2110_ = ((size_t)31ULL);
v___x_2111_ = lean_usize_land(v_x_2105_, v___x_2110_);
v_j_2112_ = lean_usize_to_nat(v___x_2111_);
v___x_2113_ = lean_array_get_size(v_es_2109_);
v___x_2114_ = lean_nat_dec_lt(v_j_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_dec(v_j_2112_);
lean_dec(v_x_2108_);
lean_dec_ref(v_x_2107_);
return v_x_2104_;
}
else
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2155_; 
lean_inc_ref(v_es_2109_);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_x_2104_, 0);
lean_dec(v_unused_2156_);
v___x_2116_ = v_x_2104_;
v_isShared_2117_ = v_isSharedCheck_2155_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v_x_2104_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2155_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_v_2118_; lean_object* v___x_2119_; lean_object* v_xs_x27_2120_; lean_object* v___y_2122_; 
v_v_2118_ = lean_array_fget(v_es_2109_, v_j_2112_);
v___x_2119_ = lean_box(0);
v_xs_x27_2120_ = lean_array_fset(v_es_2109_, v_j_2112_, v___x_2119_);
switch(lean_obj_tag(v_v_2118_))
{
case 0:
{
lean_object* v_key_2127_; lean_object* v_val_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2140_; 
v_key_2127_ = lean_ctor_get(v_v_2118_, 0);
v_val_2128_ = lean_ctor_get(v_v_2118_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_v_2118_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2130_ = v_v_2118_;
v_isShared_2131_ = v_isSharedCheck_2140_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_val_2128_);
lean_inc(v_key_2127_);
lean_dec(v_v_2118_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2140_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = lean_ptr_addr(v_x_2107_);
v___x_2133_ = lean_ptr_addr(v_key_2127_);
v___x_2134_ = lean_usize_dec_eq(v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_del_object(v___x_2130_);
v___x_2135_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2127_, v_val_2128_, v_x_2107_, v_x_2108_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___y_2122_ = v___x_2136_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2138_; 
lean_dec(v_val_2128_);
lean_dec(v_key_2127_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_x_2108_);
lean_ctor_set(v___x_2130_, 0, v_x_2107_);
v___x_2138_ = v___x_2130_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_x_2107_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_x_2108_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
v___y_2122_ = v___x_2138_;
goto v___jp_2121_;
}
}
}
}
case 1:
{
lean_object* v_node_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2153_; 
v_node_2141_ = lean_ctor_get(v_v_2118_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_v_2118_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2143_ = v_v_2118_;
v_isShared_2144_ = v_isSharedCheck_2153_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_node_2141_);
lean_dec(v_v_2118_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2153_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
size_t v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2145_ = ((size_t)5ULL);
v___x_2146_ = lean_usize_shift_right(v_x_2105_, v___x_2145_);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_x_2106_, v___x_2147_);
v___x_2149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2141_, v___x_2146_, v___x_2148_, v_x_2107_, v_x_2108_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2149_);
v___x_2151_ = v___x_2143_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
v___y_2122_ = v___x_2151_;
goto v___jp_2121_;
}
}
}
default: 
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_x_2107_);
lean_ctor_set(v___x_2154_, 1, v_x_2108_);
v___y_2122_ = v___x_2154_;
goto v___jp_2121_;
}
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_array_fset(v_xs_x27_2120_, v_j_2112_, v___y_2122_);
lean_dec(v_j_2112_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2123_);
v___x_2125_ = v___x_2116_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_object* v_ks_2157_; lean_object* v_vs_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2176_; 
v_ks_2157_ = lean_ctor_get(v_x_2104_, 0);
v_vs_2158_ = lean_ctor_get(v_x_2104_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2160_ = v_x_2104_;
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_vs_2158_);
lean_inc(v_ks_2157_);
lean_dec(v_x_2104_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_ks_2157_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_vs_2158_);
v___x_2163_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v_newNode_2164_; size_t v___x_2165_; uint8_t v___x_2166_; 
v_newNode_2164_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2163_, v_x_2107_, v_x_2108_);
v___x_2165_ = ((size_t)7ULL);
v___x_2166_ = lean_usize_dec_le(v___x_2165_, v_x_2106_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2167_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2164_);
v___x_2168_ = lean_unsigned_to_nat(4u);
v___x_2169_ = lean_nat_dec_lt(v___x_2167_, v___x_2168_);
lean_dec(v___x_2167_);
if (v___x_2169_ == 0)
{
lean_object* v_ks_2170_; lean_object* v_vs_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_ks_2170_ = lean_ctor_get(v_newNode_2164_, 0);
lean_inc_ref(v_ks_2170_);
v_vs_2171_ = lean_ctor_get(v_newNode_2164_, 1);
lean_inc_ref(v_vs_2171_);
lean_dec_ref(v_newNode_2164_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2106_, v_ks_2170_, v_vs_2171_, v___x_2172_, v___x_2173_);
lean_dec_ref(v_vs_2171_);
lean_dec_ref(v_ks_2170_);
return v___x_2174_;
}
else
{
return v_newNode_2164_;
}
}
else
{
return v_newNode_2164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2177_, lean_object* v_keys_2178_, lean_object* v_vals_2179_, lean_object* v_i_2180_, lean_object* v_entries_2181_){
_start:
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_array_get_size(v_keys_2178_);
v___x_2183_ = lean_nat_dec_lt(v_i_2180_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_dec(v_i_2180_);
return v_entries_2181_;
}
else
{
lean_object* v_k_2184_; lean_object* v_v_2185_; size_t v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; uint64_t v___x_2189_; size_t v_h_2190_; size_t v___x_2191_; lean_object* v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; size_t v_h_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_k_2184_ = lean_array_fget_borrowed(v_keys_2178_, v_i_2180_);
v_v_2185_ = lean_array_fget_borrowed(v_vals_2179_, v_i_2180_);
v___x_2186_ = lean_ptr_addr(v_k_2184_);
v___x_2187_ = ((size_t)3ULL);
v___x_2188_ = lean_usize_shift_right(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_usize_to_uint64(v___x_2188_);
v_h_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = ((size_t)5ULL);
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_sub(v_depth_2177_, v___x_2193_);
v___x_2195_ = lean_usize_mul(v___x_2191_, v___x_2194_);
v_h_2196_ = lean_usize_shift_right(v_h_2190_, v___x_2195_);
v___x_2197_ = lean_nat_add(v_i_2180_, v___x_2192_);
lean_dec(v_i_2180_);
lean_inc(v_v_2185_);
lean_inc(v_k_2184_);
v___x_2198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2181_, v_h_2196_, v_depth_2177_, v_k_2184_, v_v_2185_);
v_i_2180_ = v___x_2197_;
v_entries_2181_ = v___x_2198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2200_, lean_object* v_keys_2201_, lean_object* v_vals_2202_, lean_object* v_i_2203_, lean_object* v_entries_2204_){
_start:
{
size_t v_depth_boxed_2205_; lean_object* v_res_2206_; 
v_depth_boxed_2205_ = lean_unbox_usize(v_depth_2200_);
lean_dec(v_depth_2200_);
v_res_2206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2205_, v_keys_2201_, v_vals_2202_, v_i_2203_, v_entries_2204_);
lean_dec_ref(v_vals_2202_);
lean_dec_ref(v_keys_2201_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
size_t v_x_6667__boxed_2212_; size_t v_x_6668__boxed_2213_; lean_object* v_res_2214_; 
v_x_6667__boxed_2212_ = lean_unbox_usize(v_x_2208_);
lean_dec(v_x_2208_);
v_x_6668__boxed_2213_ = lean_unbox_usize(v_x_2209_);
lean_dec(v_x_2209_);
v_res_2214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2207_, v_x_6667__boxed_2212_, v_x_6668__boxed_2213_, v_x_2210_, v_x_2211_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; uint64_t v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2218_ = lean_ptr_addr(v_x_2216_);
v___x_2219_ = ((size_t)3ULL);
v___x_2220_ = lean_usize_shift_right(v___x_2218_, v___x_2219_);
v___x_2221_ = lean_usize_to_uint64(v___x_2220_);
v___x_2222_ = lean_uint64_to_usize(v___x_2221_);
v___x_2223_ = ((size_t)1ULL);
v___x_2224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2215_, v___x_2222_, v___x_2223_, v_x_2216_, v_x_2217_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2225_, lean_object* v_ringId_2226_, lean_object* v_s_2227_){
_start:
{
lean_object* v_rings_2228_; lean_object* v_typeIdOf_2229_; lean_object* v_exprToRingId_2230_; lean_object* v_semirings_2231_; lean_object* v_stypeIdOf_2232_; lean_object* v_exprToSemiringId_2233_; lean_object* v_ncRings_2234_; lean_object* v_exprToNCRingId_2235_; lean_object* v_nctypeIdOf_2236_; lean_object* v_ncSemirings_2237_; lean_object* v_exprToNCSemiringId_2238_; lean_object* v_ncstypeIdOf_2239_; lean_object* v_steps_2240_; uint8_t v_reportedMaxDegreeIssue_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_rings_2228_ = lean_ctor_get(v_s_2227_, 0);
v_typeIdOf_2229_ = lean_ctor_get(v_s_2227_, 1);
v_exprToRingId_2230_ = lean_ctor_get(v_s_2227_, 2);
v_semirings_2231_ = lean_ctor_get(v_s_2227_, 3);
v_stypeIdOf_2232_ = lean_ctor_get(v_s_2227_, 4);
v_exprToSemiringId_2233_ = lean_ctor_get(v_s_2227_, 5);
v_ncRings_2234_ = lean_ctor_get(v_s_2227_, 6);
v_exprToNCRingId_2235_ = lean_ctor_get(v_s_2227_, 7);
v_nctypeIdOf_2236_ = lean_ctor_get(v_s_2227_, 8);
v_ncSemirings_2237_ = lean_ctor_get(v_s_2227_, 9);
v_exprToNCSemiringId_2238_ = lean_ctor_get(v_s_2227_, 10);
v_ncstypeIdOf_2239_ = lean_ctor_get(v_s_2227_, 11);
v_steps_2240_ = lean_ctor_get(v_s_2227_, 12);
v_reportedMaxDegreeIssue_2241_ = lean_ctor_get_uint8(v_s_2227_, sizeof(void*)*13);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_s_2227_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v_s_2227_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_steps_2240_);
lean_inc(v_ncstypeIdOf_2239_);
lean_inc(v_exprToNCSemiringId_2238_);
lean_inc(v_ncSemirings_2237_);
lean_inc(v_nctypeIdOf_2236_);
lean_inc(v_exprToNCRingId_2235_);
lean_inc(v_ncRings_2234_);
lean_inc(v_exprToSemiringId_2233_);
lean_inc(v_stypeIdOf_2232_);
lean_inc(v_semirings_2231_);
lean_inc(v_exprToRingId_2230_);
lean_inc(v_typeIdOf_2229_);
lean_inc(v_rings_2228_);
lean_dec(v_s_2227_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2230_, v_e_2225_, v_ringId_2226_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 2, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_rings_2228_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_typeIdOf_2229_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_semirings_2231_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_stypeIdOf_2232_);
lean_ctor_set(v_reuseFailAlloc_2248_, 5, v_exprToSemiringId_2233_);
lean_ctor_set(v_reuseFailAlloc_2248_, 6, v_ncRings_2234_);
lean_ctor_set(v_reuseFailAlloc_2248_, 7, v_exprToNCRingId_2235_);
lean_ctor_set(v_reuseFailAlloc_2248_, 8, v_nctypeIdOf_2236_);
lean_ctor_set(v_reuseFailAlloc_2248_, 9, v_ncSemirings_2237_);
lean_ctor_set(v_reuseFailAlloc_2248_, 10, v_exprToNCSemiringId_2238_);
lean_ctor_set(v_reuseFailAlloc_2248_, 11, v_ncstypeIdOf_2239_);
lean_ctor_set(v_reuseFailAlloc_2248_, 12, v_steps_2240_);
lean_ctor_set_uint8(v_reuseFailAlloc_2248_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2241_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2253_, v_a_2255_, v_a_2260_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
if (lean_obj_tag(v_a_2267_) == 1)
{
lean_object* v_ringId_2268_; lean_object* v_val_2269_; uint8_t v___x_2270_; 
v_ringId_2268_ = lean_ctor_get(v_a_2254_, 0);
v_val_2269_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v_a_2267_, 1);
v___x_2270_ = lean_nat_dec_eq(v_val_2269_, v_ringId_2268_);
lean_dec(v_val_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2256_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; uint8_t v_verbose_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_verbose_2273_ = lean_ctor_get_uint8(v_a_2272_, 0);
lean_dec(v_a_2272_);
if (v_verbose_2273_ == 0)
{
lean_dec_ref(v_e_2253_);
goto v___jp_2263_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2274_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2275_ = l_Lean_indentExpr(v_e_2253_);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_Meta_Sym_reportIssue(v___x_2276_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref_known(v___x_2277_, 1);
goto v___jp_2263_;
}
else
{
return v___x_2277_;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_e_2253_);
v_a_2278_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2271_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2271_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_dec_ref(v_e_2253_);
goto v___jp_2263_;
}
}
else
{
lean_object* v_ringId_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v_a_2267_);
v_ringId_2286_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_ringId_2286_);
v___f_2287_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2287_, 0, v_e_2253_);
lean_closure_set(v___f_2287_, 1, v_ringId_2286_);
v___x_2288_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2289_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2288_, v___f_2287_, v_a_2255_);
return v___x_2289_;
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_e_2253_);
v_a_2290_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2266_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2266_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
v___jp_2263_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2309_, v_a_2310_, v_a_2311_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2338_, v_x_2339_, v_x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, size_t v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2343_, v_x_2344_, v_x_2345_, v_x_2346_, v_x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
size_t v_x_6953__boxed_2355_; size_t v_x_6954__boxed_2356_; lean_object* v_res_2357_; 
v_x_6953__boxed_2355_ = lean_unbox_usize(v_x_2351_);
lean_dec(v_x_2351_);
v_x_6954__boxed_2356_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2349_, v_x_2350_, v_x_6953__boxed_2355_, v_x_6954__boxed_2356_, v_x_2353_, v_x_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2358_, lean_object* v_n_2359_, lean_object* v_k_2360_, lean_object* v_v_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2359_, v_k_2360_, v_v_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2363_, size_t v_depth_2364_, lean_object* v_keys_2365_, lean_object* v_vals_2366_, lean_object* v_heq_2367_, lean_object* v_i_2368_, lean_object* v_entries_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2364_, v_keys_2365_, v_vals_2366_, v_i_2368_, v_entries_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2371_, lean_object* v_depth_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_heq_2375_, lean_object* v_i_2376_, lean_object* v_entries_2377_){
_start:
{
size_t v_depth_boxed_2378_; lean_object* v_res_2379_; 
v_depth_boxed_2378_ = lean_unbox_usize(v_depth_2372_);
lean_dec(v_depth_2372_);
v_res_2379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2371_, v_depth_boxed_2378_, v_keys_2373_, v_vals_2374_, v_heq_2375_, v_i_2376_, v_entries_2377_);
lean_dec_ref(v_vals_2374_);
lean_dec_ref(v_keys_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2381_, v_x_2382_, v_x_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2386_, lean_object* v___f_2387_, lean_object* v___f_2388_, lean_object* v_size_2389_, lean_object* v_s_2390_){
_start:
{
lean_object* v_id_2391_; lean_object* v_type_2392_; lean_object* v_u_2393_; lean_object* v_ringInst_2394_; lean_object* v_semiringInst_2395_; lean_object* v_charInst_x3f_2396_; lean_object* v_addFn_x3f_2397_; lean_object* v_mulFn_x3f_2398_; lean_object* v_subFn_x3f_2399_; lean_object* v_negFn_x3f_2400_; lean_object* v_powFn_x3f_2401_; lean_object* v_intCastFn_x3f_2402_; lean_object* v_natCastFn_x3f_2403_; lean_object* v_one_x3f_2404_; lean_object* v_vars_2405_; lean_object* v_varMap_2406_; lean_object* v_denote_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
v_id_2391_ = lean_ctor_get(v_s_2390_, 0);
v_type_2392_ = lean_ctor_get(v_s_2390_, 1);
v_u_2393_ = lean_ctor_get(v_s_2390_, 2);
v_ringInst_2394_ = lean_ctor_get(v_s_2390_, 3);
v_semiringInst_2395_ = lean_ctor_get(v_s_2390_, 4);
v_charInst_x3f_2396_ = lean_ctor_get(v_s_2390_, 5);
v_addFn_x3f_2397_ = lean_ctor_get(v_s_2390_, 6);
v_mulFn_x3f_2398_ = lean_ctor_get(v_s_2390_, 7);
v_subFn_x3f_2399_ = lean_ctor_get(v_s_2390_, 8);
v_negFn_x3f_2400_ = lean_ctor_get(v_s_2390_, 9);
v_powFn_x3f_2401_ = lean_ctor_get(v_s_2390_, 10);
v_intCastFn_x3f_2402_ = lean_ctor_get(v_s_2390_, 11);
v_natCastFn_x3f_2403_ = lean_ctor_get(v_s_2390_, 12);
v_one_x3f_2404_ = lean_ctor_get(v_s_2390_, 13);
v_vars_2405_ = lean_ctor_get(v_s_2390_, 14);
v_varMap_2406_ = lean_ctor_get(v_s_2390_, 15);
v_denote_2407_ = lean_ctor_get(v_s_2390_, 16);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_s_2390_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v_s_2390_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_denote_2407_);
lean_inc(v_varMap_2406_);
lean_inc(v_vars_2405_);
lean_inc(v_one_x3f_2404_);
lean_inc(v_natCastFn_x3f_2403_);
lean_inc(v_intCastFn_x3f_2402_);
lean_inc(v_powFn_x3f_2401_);
lean_inc(v_negFn_x3f_2400_);
lean_inc(v_subFn_x3f_2399_);
lean_inc(v_mulFn_x3f_2398_);
lean_inc(v_addFn_x3f_2397_);
lean_inc(v_charInst_x3f_2396_);
lean_inc(v_semiringInst_2395_);
lean_inc(v_ringInst_2394_);
lean_inc(v_u_2393_);
lean_inc(v_type_2392_);
lean_inc(v_id_2391_);
lean_dec(v_s_2390_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_inc_ref(v_e_2386_);
v___x_2411_ = l_Lean_PersistentArray_push___redArg(v_vars_2405_, v_e_2386_);
v___x_2412_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2387_, v___f_2388_, v_varMap_2406_, v_e_2386_, v_size_2389_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 15, v___x_2412_);
lean_ctor_set(v___x_2409_, 14, v___x_2411_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_id_2391_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_type_2392_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v_u_2393_);
lean_ctor_set(v_reuseFailAlloc_2415_, 3, v_ringInst_2394_);
lean_ctor_set(v_reuseFailAlloc_2415_, 4, v_semiringInst_2395_);
lean_ctor_set(v_reuseFailAlloc_2415_, 5, v_charInst_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2415_, 6, v_addFn_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2415_, 7, v_mulFn_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2415_, 8, v_subFn_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2415_, 9, v_negFn_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2415_, 10, v_powFn_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2415_, 11, v_intCastFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2415_, 12, v_natCastFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2415_, 13, v_one_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2415_, 14, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 15, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2415_, 16, v_denote_2407_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2417_, lean_object* v_size_2418_, lean_object* v_____r_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_apply_2(v_toPure_2417_, lean_box(0), v_size_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2421_, lean_object* v_inst_2422_, lean_object* v_toBind_2423_, lean_object* v___f_2424_, lean_object* v_____r_2425_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2427_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2427_, 0, lean_box(0));
lean_closure_set(v___x_2427_, 1, v___x_2426_);
lean_closure_set(v___x_2427_, 2, v_e_2421_);
v___x_2428_ = lean_apply_2(v_inst_2422_, lean_box(0), v___x_2427_);
v___x_2429_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2428_, v___f_2424_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2430_, lean_object* v_e_2431_, lean_object* v_toBind_2432_, lean_object* v___f_2433_, lean_object* v_____r_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_apply_1(v_inst_2430_, v_e_2431_);
v___x_2436_ = lean_apply_4(v_toBind_2432_, lean_box(0), lean_box(0), v___x_2435_, v___f_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2437_, lean_object* v___f_2438_, lean_object* v_e_2439_, lean_object* v_toPure_2440_, lean_object* v_inst_2441_, lean_object* v_toBind_2442_, lean_object* v_inst_2443_, lean_object* v_modifyRing_2444_, lean_object* v_s_2445_){
_start:
{
lean_object* v_vars_2446_; lean_object* v_varMap_2447_; lean_object* v___x_2448_; 
v_vars_2446_ = lean_ctor_get(v_s_2445_, 14);
lean_inc_ref(v_vars_2446_);
v_varMap_2447_ = lean_ctor_get(v_s_2445_, 15);
lean_inc_ref(v_varMap_2447_);
lean_dec_ref(v_s_2445_);
lean_inc_ref(v_e_2439_);
lean_inc_ref(v___f_2438_);
lean_inc_ref(v___f_2437_);
v___x_2448_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2437_, v___f_2438_, v_varMap_2447_, v_e_2439_);
lean_dec_ref(v_varMap_2447_);
if (lean_obj_tag(v___x_2448_) == 1)
{
lean_object* v_val_2449_; lean_object* v___x_2450_; 
lean_dec_ref(v_vars_2446_);
lean_dec(v_modifyRing_2444_);
lean_dec(v_inst_2443_);
lean_dec(v_toBind_2442_);
lean_dec(v_inst_2441_);
lean_dec_ref(v_e_2439_);
lean_dec_ref(v___f_2438_);
lean_dec_ref(v___f_2437_);
v_val_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_val_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_apply_2(v_toPure_2440_, lean_box(0), v_val_2449_);
return v___x_2450_;
}
else
{
lean_object* v_size_2451_; lean_object* v___f_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_dec(v___x_2448_);
v_size_2451_ = lean_ctor_get(v_vars_2446_, 2);
lean_inc_n(v_size_2451_, 2);
lean_dec_ref(v_vars_2446_);
lean_inc_ref_n(v_e_2439_, 2);
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2452_, 0, v_e_2439_);
lean_closure_set(v___f_2452_, 1, v___f_2437_);
lean_closure_set(v___f_2452_, 2, v___f_2438_);
lean_closure_set(v___f_2452_, 3, v_size_2451_);
v___f_2453_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2453_, 0, v_toPure_2440_);
lean_closure_set(v___f_2453_, 1, v_size_2451_);
lean_inc_n(v_toBind_2442_, 2);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2454_, 0, v_e_2439_);
lean_closure_set(v___f_2454_, 1, v_inst_2441_);
lean_closure_set(v___f_2454_, 2, v_toBind_2442_);
lean_closure_set(v___f_2454_, 3, v___f_2453_);
v___f_2455_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2455_, 0, v_inst_2443_);
lean_closure_set(v___f_2455_, 1, v_e_2439_);
lean_closure_set(v___f_2455_, 2, v_toBind_2442_);
lean_closure_set(v___f_2455_, 3, v___f_2454_);
v___x_2456_ = lean_apply_1(v_modifyRing_2444_, v___f_2452_);
v___x_2457_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2456_, v___f_2455_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_e_2464_){
_start:
{
lean_object* v_toApplicative_2465_; lean_object* v_toBind_2466_; lean_object* v_getRing_2467_; lean_object* v_modifyRing_2468_; lean_object* v_toPure_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; 
v_toApplicative_2465_ = lean_ctor_get(v_inst_2461_, 0);
lean_inc_ref(v_toApplicative_2465_);
v_toBind_2466_ = lean_ctor_get(v_inst_2461_, 1);
lean_inc_n(v_toBind_2466_, 2);
lean_dec_ref(v_inst_2461_);
v_getRing_2467_ = lean_ctor_get(v_inst_2462_, 0);
lean_inc(v_getRing_2467_);
v_modifyRing_2468_ = lean_ctor_get(v_inst_2462_, 1);
lean_inc(v_modifyRing_2468_);
lean_dec_ref(v_inst_2462_);
v_toPure_2469_ = lean_ctor_get(v_toApplicative_2465_, 1);
lean_inc(v_toPure_2469_);
lean_dec_ref(v_toApplicative_2465_);
v___f_2470_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2472_, 0, v___f_2470_);
lean_closure_set(v___f_2472_, 1, v___f_2471_);
lean_closure_set(v___f_2472_, 2, v_e_2464_);
lean_closure_set(v___f_2472_, 3, v_toPure_2469_);
lean_closure_set(v___f_2472_, 4, v_inst_2460_);
lean_closure_set(v___f_2472_, 5, v_toBind_2466_);
lean_closure_set(v___f_2472_, 6, v_inst_2463_);
lean_closure_set(v___f_2472_, 7, v_modifyRing_2468_);
v___x_2473_ = lean_apply_4(v_toBind_2466_, lean_box(0), lean_box(0), v_getRing_2467_, v___f_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_e_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2475_, v_inst_2476_, v_inst_2477_, v_inst_2478_, v_e_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2481_, v___y_2482_, v___y_2483_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2511_, lean_object* v_size_2512_, lean_object* v_s_2513_){
_start:
{
lean_object* v_toRing_2514_; lean_object* v_invFn_x3f_2515_; lean_object* v_semiringId_x3f_2516_; lean_object* v_commSemiringInst_2517_; lean_object* v_commRingInst_2518_; lean_object* v_noZeroDivInst_x3f_2519_; lean_object* v_fieldInst_x3f_2520_; lean_object* v_powIdentityInst_x3f_2521_; lean_object* v_denoteEntries_2522_; lean_object* v_nextId_2523_; lean_object* v_steps_2524_; lean_object* v_queue_2525_; lean_object* v_basis_2526_; lean_object* v_diseqs_2527_; uint8_t v_recheck_2528_; lean_object* v_invSet_2529_; lean_object* v_powIdentityVarCount_2530_; lean_object* v_numEq0_x3f_2531_; uint8_t v_numEq0Updated_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2565_; 
v_toRing_2514_ = lean_ctor_get(v_s_2513_, 0);
v_invFn_x3f_2515_ = lean_ctor_get(v_s_2513_, 1);
v_semiringId_x3f_2516_ = lean_ctor_get(v_s_2513_, 2);
v_commSemiringInst_2517_ = lean_ctor_get(v_s_2513_, 3);
v_commRingInst_2518_ = lean_ctor_get(v_s_2513_, 4);
v_noZeroDivInst_x3f_2519_ = lean_ctor_get(v_s_2513_, 5);
v_fieldInst_x3f_2520_ = lean_ctor_get(v_s_2513_, 6);
v_powIdentityInst_x3f_2521_ = lean_ctor_get(v_s_2513_, 7);
v_denoteEntries_2522_ = lean_ctor_get(v_s_2513_, 8);
v_nextId_2523_ = lean_ctor_get(v_s_2513_, 9);
v_steps_2524_ = lean_ctor_get(v_s_2513_, 10);
v_queue_2525_ = lean_ctor_get(v_s_2513_, 11);
v_basis_2526_ = lean_ctor_get(v_s_2513_, 12);
v_diseqs_2527_ = lean_ctor_get(v_s_2513_, 13);
v_recheck_2528_ = lean_ctor_get_uint8(v_s_2513_, sizeof(void*)*17);
v_invSet_2529_ = lean_ctor_get(v_s_2513_, 14);
v_powIdentityVarCount_2530_ = lean_ctor_get(v_s_2513_, 15);
v_numEq0_x3f_2531_ = lean_ctor_get(v_s_2513_, 16);
v_numEq0Updated_2532_ = lean_ctor_get_uint8(v_s_2513_, sizeof(void*)*17 + 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_s_2513_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2534_ = v_s_2513_;
v_isShared_2535_ = v_isSharedCheck_2565_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_numEq0_x3f_2531_);
lean_inc(v_powIdentityVarCount_2530_);
lean_inc(v_invSet_2529_);
lean_inc(v_diseqs_2527_);
lean_inc(v_basis_2526_);
lean_inc(v_queue_2525_);
lean_inc(v_steps_2524_);
lean_inc(v_nextId_2523_);
lean_inc(v_denoteEntries_2522_);
lean_inc(v_powIdentityInst_x3f_2521_);
lean_inc(v_fieldInst_x3f_2520_);
lean_inc(v_noZeroDivInst_x3f_2519_);
lean_inc(v_commRingInst_2518_);
lean_inc(v_commSemiringInst_2517_);
lean_inc(v_semiringId_x3f_2516_);
lean_inc(v_invFn_x3f_2515_);
lean_inc(v_toRing_2514_);
lean_dec(v_s_2513_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2565_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_id_2536_; lean_object* v_type_2537_; lean_object* v_u_2538_; lean_object* v_ringInst_2539_; lean_object* v_semiringInst_2540_; lean_object* v_charInst_x3f_2541_; lean_object* v_addFn_x3f_2542_; lean_object* v_mulFn_x3f_2543_; lean_object* v_subFn_x3f_2544_; lean_object* v_negFn_x3f_2545_; lean_object* v_powFn_x3f_2546_; lean_object* v_intCastFn_x3f_2547_; lean_object* v_natCastFn_x3f_2548_; lean_object* v_one_x3f_2549_; lean_object* v_vars_2550_; lean_object* v_varMap_2551_; lean_object* v_denote_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2564_; 
v_id_2536_ = lean_ctor_get(v_toRing_2514_, 0);
v_type_2537_ = lean_ctor_get(v_toRing_2514_, 1);
v_u_2538_ = lean_ctor_get(v_toRing_2514_, 2);
v_ringInst_2539_ = lean_ctor_get(v_toRing_2514_, 3);
v_semiringInst_2540_ = lean_ctor_get(v_toRing_2514_, 4);
v_charInst_x3f_2541_ = lean_ctor_get(v_toRing_2514_, 5);
v_addFn_x3f_2542_ = lean_ctor_get(v_toRing_2514_, 6);
v_mulFn_x3f_2543_ = lean_ctor_get(v_toRing_2514_, 7);
v_subFn_x3f_2544_ = lean_ctor_get(v_toRing_2514_, 8);
v_negFn_x3f_2545_ = lean_ctor_get(v_toRing_2514_, 9);
v_powFn_x3f_2546_ = lean_ctor_get(v_toRing_2514_, 10);
v_intCastFn_x3f_2547_ = lean_ctor_get(v_toRing_2514_, 11);
v_natCastFn_x3f_2548_ = lean_ctor_get(v_toRing_2514_, 12);
v_one_x3f_2549_ = lean_ctor_get(v_toRing_2514_, 13);
v_vars_2550_ = lean_ctor_get(v_toRing_2514_, 14);
v_varMap_2551_ = lean_ctor_get(v_toRing_2514_, 15);
v_denote_2552_ = lean_ctor_get(v_toRing_2514_, 16);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_toRing_2514_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2554_ = v_toRing_2514_;
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_denote_2552_);
lean_inc(v_varMap_2551_);
lean_inc(v_vars_2550_);
lean_inc(v_one_x3f_2549_);
lean_inc(v_natCastFn_x3f_2548_);
lean_inc(v_intCastFn_x3f_2547_);
lean_inc(v_powFn_x3f_2546_);
lean_inc(v_negFn_x3f_2545_);
lean_inc(v_subFn_x3f_2544_);
lean_inc(v_mulFn_x3f_2543_);
lean_inc(v_addFn_x3f_2542_);
lean_inc(v_charInst_x3f_2541_);
lean_inc(v_semiringInst_2540_);
lean_inc(v_ringInst_2539_);
lean_inc(v_u_2538_);
lean_inc(v_type_2537_);
lean_inc(v_id_2536_);
lean_dec(v_toRing_2514_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2564_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_inc_ref(v_e_2511_);
v___x_2556_ = l_Lean_PersistentArray_push___redArg(v_vars_2550_, v_e_2511_);
v___x_2557_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2551_, v_e_2511_, v_size_2512_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 15, v___x_2557_);
lean_ctor_set(v___x_2554_, 14, v___x_2556_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_id_2536_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_type_2537_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_u_2538_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_ringInst_2539_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_semiringInst_2540_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_charInst_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_addFn_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v_mulFn_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v_subFn_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2563_, 9, v_negFn_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2563_, 10, v_powFn_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2563_, 11, v_intCastFn_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2563_, 12, v_natCastFn_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2563_, 13, v_one_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2563_, 14, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2563_, 15, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2563_, 16, v_denote_2552_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2559_);
v___x_2561_ = v___x_2534_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_invFn_x3f_2515_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_semiringId_x3f_2516_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_commSemiringInst_2517_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_commRingInst_2518_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v_noZeroDivInst_x3f_2519_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_fieldInst_x3f_2520_);
lean_ctor_set(v_reuseFailAlloc_2562_, 7, v_powIdentityInst_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2562_, 8, v_denoteEntries_2522_);
lean_ctor_set(v_reuseFailAlloc_2562_, 9, v_nextId_2523_);
lean_ctor_set(v_reuseFailAlloc_2562_, 10, v_steps_2524_);
lean_ctor_set(v_reuseFailAlloc_2562_, 11, v_queue_2525_);
lean_ctor_set(v_reuseFailAlloc_2562_, 12, v_basis_2526_);
lean_ctor_set(v_reuseFailAlloc_2562_, 13, v_diseqs_2527_);
lean_ctor_set(v_reuseFailAlloc_2562_, 14, v_invSet_2529_);
lean_ctor_set(v_reuseFailAlloc_2562_, 15, v_powIdentityVarCount_2530_);
lean_ctor_set(v_reuseFailAlloc_2562_, 16, v_numEq0_x3f_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*17, v_recheck_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*17 + 1, v_numEq0Updated_2532_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2630_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2630_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2630_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_toRing_2584_; lean_object* v_vars_2585_; lean_object* v_varMap_2586_; lean_object* v___x_2587_; 
v_toRing_2584_ = lean_ctor_get(v_a_2580_, 0);
lean_inc_ref(v_toRing_2584_);
lean_dec(v_a_2580_);
v_vars_2585_ = lean_ctor_get(v_toRing_2584_, 14);
lean_inc_ref(v_vars_2585_);
v_varMap_2586_ = lean_ctor_get(v_toRing_2584_, 15);
lean_inc_ref(v_varMap_2586_);
lean_dec_ref(v_toRing_2584_);
v___x_2587_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2586_, v_e_2566_);
lean_dec_ref(v_varMap_2586_);
if (lean_obj_tag(v___x_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2590_; 
lean_dec_ref(v_vars_2585_);
lean_dec_ref(v_e_2566_);
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2587_, 1);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v_val_2588_);
v___x_2590_ = v___x_2582_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_val_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_object* v_size_2592_; lean_object* v___f_2593_; lean_object* v___x_2594_; 
lean_dec(v___x_2587_);
lean_del_object(v___x_2582_);
v_size_2592_ = lean_ctor_get(v_vars_2585_, 2);
lean_inc_n(v_size_2592_, 2);
lean_dec_ref(v_vars_2585_);
lean_inc_ref(v_e_2566_);
v___f_2593_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2593_, 0, v_e_2566_);
lean_closure_set(v___f_2593_, 1, v_size_2592_);
v___x_2594_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2593_, v___y_2567_, v___y_2568_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; 
lean_dec_ref_known(v___x_2594_, 1);
lean_inc_ref(v_e_2566_);
v___x_2595_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2566_, v___y_2567_, v___y_2568_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2595_, 1);
v___x_2596_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2597_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2596_, v_e_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v___x_2597_, 0);
lean_dec(v_unused_2605_);
v___x_2599_ = v___x_2597_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_dec(v___x_2597_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v_size_2592_);
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_size_2592_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_size_2592_);
v_a_2606_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2597_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2597_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec(v_size_2592_);
lean_dec_ref(v_e_2566_);
v_a_2614_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2595_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2595_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_size_2592_);
lean_dec_ref(v_e_2566_);
v_a_2622_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2594_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2594_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v_e_2566_);
v_a_2631_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2579_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2579_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2680_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
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
