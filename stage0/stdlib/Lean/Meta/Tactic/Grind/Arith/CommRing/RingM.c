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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_k_x27_796_; uint8_t v___x_797_; 
v_k_x27_796_ = lean_array_fget_borrowed(v_keys_789_, v_i_791_);
v___x_797_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_792_, v_k_x27_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_i_791_, v___x_798_);
lean_dec(v_i_791_);
v_i_791_ = v___x_799_;
goto _start;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_array_fget_borrowed(v_vals_790_, v_i_791_);
lean_dec(v_i_791_);
lean_inc(v___x_801_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_803_, v_vals_804_, v_i_805_, v_k_806_);
lean_dec_ref(v_k_806_);
lean_dec_ref(v_vals_804_);
lean_dec_ref(v_keys_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_808_, size_t v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v_es_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v_j_815_; lean_object* v___x_816_; 
v_es_811_ = lean_ctor_get(v_x_808_, 0);
v___x_812_ = lean_box(2);
v___x_813_ = ((size_t)31ULL);
v___x_814_ = lean_usize_land(v_x_809_, v___x_813_);
v_j_815_ = lean_usize_to_nat(v___x_814_);
v___x_816_ = lean_array_get_borrowed(v___x_812_, v_es_811_, v_j_815_);
lean_dec(v_j_815_);
switch(lean_obj_tag(v___x_816_))
{
case 0:
{
lean_object* v_key_817_; lean_object* v_val_818_; uint8_t v___x_819_; 
v_key_817_ = lean_ctor_get(v___x_816_, 0);
v_val_818_ = lean_ctor_get(v___x_816_, 1);
v___x_819_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_810_, v_key_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
lean_inc(v_val_818_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_val_818_);
return v___x_821_;
}
}
case 1:
{
lean_object* v_node_822_; size_t v___x_823_; size_t v___x_824_; 
v_node_822_ = lean_ctor_get(v___x_816_, 0);
v___x_823_ = ((size_t)5ULL);
v___x_824_ = lean_usize_shift_right(v_x_809_, v___x_823_);
v_x_808_ = v_node_822_;
v_x_809_ = v___x_824_;
goto _start;
}
default: 
{
lean_object* v___x_826_; 
v___x_826_ = lean_box(0);
return v___x_826_;
}
}
}
else
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_ks_827_ = lean_ctor_get(v_x_808_, 0);
v_vs_828_ = lean_ctor_get(v_x_808_, 1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_827_, v_vs_828_, v___x_829_, v_x_810_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_866__boxed_834_; lean_object* v_res_835_; 
v_x_866__boxed_834_ = lean_unbox_usize(v_x_832_);
lean_dec(v_x_832_);
v_res_835_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_831_, v_x_866__boxed_834_, v_x_833_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_831_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint64_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_836_, v___x_839_, v_x_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_841_, v_x_842_);
lean_dec_ref(v_x_842_);
lean_dec_ref(v_x_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_exprToRingId_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_exprToRingId_853_ = lean_ctor_get(v_a_849_, 2);
lean_inc_ref(v_exprToRingId_853_);
lean_dec(v_a_849_);
v___x_854_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_853_, v_e_844_);
lean_dec_ref(v_exprToRingId_853_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_848_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_848_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_867_, v_a_868_, v_a_869_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_e_867_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_872_, v_a_873_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_e_885_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_899_, v_x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_902_, v_x_903_, v_x_904_);
lean_dec_ref(v_x_904_);
lean_dec_ref(v_x_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
size_t v_x_977__boxed_915_; lean_object* v_res_916_; 
v_x_977__boxed_915_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_911_, v_x_912_, v_x_977__boxed_915_, v_x_914_);
lean_dec_ref(v_x_914_);
lean_dec_ref(v_x_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_heq_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_918_, v_vals_919_, v_i_921_, v_k_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_k_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_924_, v_keys_925_, v_vals_926_, v_heq_927_, v_i_928_, v_k_929_);
lean_dec_ref(v_k_929_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_931_, lean_object* v_____do__lift_932_){
_start:
{
lean_object* v_charInst_x3f_936_; 
v_charInst_x3f_936_ = lean_ctor_get(v_____do__lift_932_, 5);
lean_inc(v_charInst_x3f_936_);
lean_dec_ref(v_____do__lift_932_);
if (lean_obj_tag(v_charInst_x3f_936_) == 1)
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_949_; 
v_val_937_ = lean_ctor_get(v_charInst_x3f_936_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_charInst_x3f_936_);
if (v_isSharedCheck_949_ == 0)
{
v___x_939_ = v_charInst_x3f_936_;
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v_charInst_x3f_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_snd_941_; lean_object* v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; 
v_snd_941_ = lean_ctor_get(v_val_937_, 1);
lean_inc(v_snd_941_);
lean_dec(v_val_937_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_nat_dec_eq(v_snd_941_, v___x_942_);
v___x_944_ = lean_bool_not(v___x_943_);
if (v___x_944_ == 0)
{
lean_dec(v_snd_941_);
lean_del_object(v___x_939_);
goto v___jp_933_;
}
else
{
lean_object* v___x_946_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_snd_941_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_snd_941_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_946_);
return v___x_947_;
}
}
}
}
else
{
lean_dec(v_charInst_x3f_936_);
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_box(0);
v___x_935_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v_toApplicative_952_; lean_object* v_toBind_953_; lean_object* v_getRing_954_; lean_object* v_toPure_955_; lean_object* v___f_956_; lean_object* v___x_957_; 
v_toApplicative_952_ = lean_ctor_get(v_inst_950_, 0);
lean_inc_ref(v_toApplicative_952_);
v_toBind_953_ = lean_ctor_get(v_inst_950_, 1);
lean_inc(v_toBind_953_);
lean_dec_ref(v_inst_950_);
v_getRing_954_ = lean_ctor_get(v_inst_951_, 0);
lean_inc(v_getRing_954_);
lean_dec_ref(v_inst_951_);
v_toPure_955_ = lean_ctor_get(v_toApplicative_952_, 1);
lean_inc(v_toPure_955_);
lean_dec_ref(v_toApplicative_952_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_956_, 0, v_toPure_955_);
v___x_957_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v_getRing_954_, v___f_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_inst_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_959_, v_inst_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_962_, lean_object* v_____do__lift_963_){
_start:
{
lean_object* v_charInst_x3f_967_; 
v_charInst_x3f_967_ = lean_ctor_get(v_____do__lift_963_, 5);
lean_inc(v_charInst_x3f_967_);
lean_dec_ref(v_____do__lift_963_);
if (lean_obj_tag(v_charInst_x3f_967_) == 1)
{
lean_object* v_val_968_; lean_object* v_snd_969_; lean_object* v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; 
v_val_968_ = lean_ctor_get(v_charInst_x3f_967_, 0);
v_snd_969_ = lean_ctor_get(v_val_968_, 1);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_nat_dec_eq(v_snd_969_, v___x_970_);
v___x_972_ = lean_bool_not(v___x_971_);
if (v___x_972_ == 0)
{
lean_dec_ref_known(v_charInst_x3f_967_, 1);
goto v___jp_964_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_apply_2(v_toPure_962_, lean_box(0), v_charInst_x3f_967_);
return v___x_973_;
}
}
else
{
lean_dec(v_charInst_x3f_967_);
goto v___jp_964_;
}
v___jp_964_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_box(0);
v___x_966_ = lean_apply_2(v_toPure_962_, lean_box(0), v___x_965_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v_toApplicative_976_; lean_object* v_toBind_977_; lean_object* v_getRing_978_; lean_object* v_toPure_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v_toApplicative_976_ = lean_ctor_get(v_inst_974_, 0);
lean_inc_ref(v_toApplicative_976_);
v_toBind_977_ = lean_ctor_get(v_inst_974_, 1);
lean_inc(v_toBind_977_);
lean_dec_ref(v_inst_974_);
v_getRing_978_ = lean_ctor_get(v_inst_975_, 0);
lean_inc(v_getRing_978_);
lean_dec_ref(v_inst_975_);
v_toPure_979_ = lean_ctor_get(v_toApplicative_976_, 1);
lean_inc(v_toPure_979_);
lean_dec_ref(v_toApplicative_976_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_980_, 0, v_toPure_979_);
v___x_981_ = lean_apply_4(v_toBind_977_, lean_box(0), lean_box(0), v_getRing_978_, v___f_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_982_, lean_object* v_inst_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_983_, v_inst_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_noZeroDivInst_x3f_1003_; lean_object* v___x_1005_; 
v_noZeroDivInst_x3f_1003_ = lean_ctor_get(v_a_999_, 5);
lean_inc(v_noZeroDivInst_x3f_1003_);
lean_dec(v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_noZeroDivInst_x3f_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_noZeroDivInst_x3f_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_998_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_998_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1057_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1057_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1057_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_noZeroDivInst_x3f_1046_; 
v_noZeroDivInst_x3f_1046_ = lean_ctor_get(v_a_1042_, 5);
lean_inc(v_noZeroDivInst_x3f_1046_);
lean_dec(v_a_1042_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1046_) == 0)
{
uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = 0;
v___x_1048_ = lean_box(v___x_1047_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1048_);
v___x_1050_ = v___x_1044_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1046_, 1);
v___x_1052_ = 1;
v___x_1053_ = lean_box(v___x_1052_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1053_);
v___x_1055_ = v___x_1044_;
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
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1041_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1041_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1108_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1108_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1108_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_toRing_1096_; lean_object* v_charInst_x3f_1097_; 
v_toRing_1096_ = lean_ctor_get(v_a_1092_, 0);
lean_inc_ref(v_toRing_1096_);
lean_dec(v_a_1092_);
v_charInst_x3f_1097_ = lean_ctor_get(v_toRing_1096_, 5);
lean_inc(v_charInst_x3f_1097_);
lean_dec_ref(v_toRing_1096_);
if (lean_obj_tag(v_charInst_x3f_1097_) == 0)
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1098_ = 0;
v___x_1099_ = lean_box(v___x_1098_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1099_);
v___x_1101_ = v___x_1094_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec_ref_known(v_charInst_x3f_1097_, 1);
v___x_1103_ = 1;
v___x_1104_ = lean_box(v___x_1103_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1104_);
v___x_1106_ = v___x_1094_;
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
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1091_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1091_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1158_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_toRing_1150_; lean_object* v_charInst_x3f_1151_; 
v_toRing_1150_ = lean_ctor_get(v_a_1146_, 0);
lean_inc_ref(v_toRing_1150_);
lean_dec(v_a_1146_);
v_charInst_x3f_1151_ = lean_ctor_get(v_toRing_1150_, 5);
lean_inc(v_charInst_x3f_1151_);
lean_dec_ref(v_toRing_1150_);
if (lean_obj_tag(v_charInst_x3f_1151_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1154_; 
v_val_1152_ = lean_ctor_get(v_charInst_x3f_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_charInst_x3f_1151_, 1);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_val_1152_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_val_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_charInst_x3f_1151_);
lean_del_object(v___x_1148_);
v___x_1156_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1157_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1156_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1145_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1145_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1208_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1208_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fieldInst_x3f_1197_; 
v_fieldInst_x3f_1197_ = lean_ctor_get(v_a_1193_, 6);
lean_inc(v_fieldInst_x3f_1197_);
lean_dec(v_a_1193_);
if (lean_obj_tag(v_fieldInst_x3f_1197_) == 0)
{
uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = 0;
v___x_1199_ = lean_box(v___x_1198_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1199_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec_ref_known(v_fieldInst_x3f_1197_, 1);
v___x_1203_ = 1;
v___x_1204_ = lean_box(v___x_1203_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1204_);
v___x_1206_ = v___x_1195_;
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
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1192_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1192_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1258_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1258_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1258_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_queue_1247_; 
v_queue_1247_ = lean_ctor_get(v_a_1243_, 11);
lean_inc(v_queue_1247_);
lean_dec(v_a_1243_);
if (lean_obj_tag(v_queue_1247_) == 0)
{
uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec_ref_known(v_queue_1247_, 5);
v___x_1248_ = 0;
v___x_1249_ = lean_box(v___x_1248_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1249_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = 1;
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1254_);
v___x_1256_ = v___x_1245_;
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
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1242_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1242_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1280_, lean_object* v_t_1281_){
_start:
{
if (lean_obj_tag(v_t_1281_) == 0)
{
lean_object* v_k_1282_; lean_object* v_v_1283_; lean_object* v_l_1284_; lean_object* v_r_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1939_; 
v_k_1282_ = lean_ctor_get(v_t_1281_, 1);
v_v_1283_ = lean_ctor_get(v_t_1281_, 2);
v_l_1284_ = lean_ctor_get(v_t_1281_, 3);
v_r_1285_ = lean_ctor_get(v_t_1281_, 4);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_t_1281_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_t_1281_, 0);
lean_dec(v_unused_1940_);
v___x_1287_ = v_t_1281_;
v_isShared_1288_ = v_isSharedCheck_1939_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_r_1285_);
lean_inc(v_l_1284_);
lean_inc(v_v_1283_);
lean_inc(v_k_1282_);
lean_dec(v_t_1281_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1939_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1280_, v_k_1282_);
switch(v___x_1289_)
{
case 0:
{
lean_object* v_impl_1290_; lean_object* v___x_1291_; 
v_impl_1290_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1280_, v_l_1284_);
v___x_1291_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1290_) == 0)
{
if (lean_obj_tag(v_r_1285_) == 0)
{
lean_object* v_size_1292_; lean_object* v_size_1293_; lean_object* v_k_1294_; lean_object* v_v_1295_; lean_object* v_l_1296_; lean_object* v_r_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_size_1292_ = lean_ctor_get(v_impl_1290_, 0);
lean_inc(v_size_1292_);
v_size_1293_ = lean_ctor_get(v_r_1285_, 0);
v_k_1294_ = lean_ctor_get(v_r_1285_, 1);
v_v_1295_ = lean_ctor_get(v_r_1285_, 2);
v_l_1296_ = lean_ctor_get(v_r_1285_, 3);
lean_inc(v_l_1296_);
v_r_1297_ = lean_ctor_get(v_r_1285_, 4);
v___x_1298_ = lean_unsigned_to_nat(3u);
v___x_1299_ = lean_nat_mul(v___x_1298_, v_size_1292_);
v___x_1300_ = lean_nat_dec_lt(v___x_1299_, v_size_1293_);
lean_dec(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec(v_l_1296_);
v___x_1301_ = lean_nat_add(v___x_1291_, v_size_1292_);
lean_dec(v_size_1292_);
v___x_1302_ = lean_nat_add(v___x_1301_, v_size_1293_);
lean_dec(v___x_1301_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 3, v_impl_1290_);
lean_ctor_set(v___x_1287_, 0, v___x_1302_);
v___x_1304_ = v___x_1287_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_impl_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_r_1285_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_r_1297_);
lean_inc(v_v_1295_);
lean_inc(v_k_1294_);
lean_inc(v_size_1293_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1370_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_r_1285_, 2);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_r_1285_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1374_);
v___x_1307_ = v_r_1285_;
v_isShared_1308_ = v_isSharedCheck_1369_;
goto v_resetjp_1306_;
}
else
{
lean_dec(v_r_1285_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1369_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_size_1309_; lean_object* v_k_1310_; lean_object* v_v_1311_; lean_object* v_l_1312_; lean_object* v_r_1313_; lean_object* v_size_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_size_1309_ = lean_ctor_get(v_l_1296_, 0);
v_k_1310_ = lean_ctor_get(v_l_1296_, 1);
v_v_1311_ = lean_ctor_get(v_l_1296_, 2);
v_l_1312_ = lean_ctor_get(v_l_1296_, 3);
v_r_1313_ = lean_ctor_get(v_l_1296_, 4);
v_size_1314_ = lean_ctor_get(v_r_1297_, 0);
v___x_1315_ = lean_unsigned_to_nat(2u);
v___x_1316_ = lean_nat_mul(v___x_1315_, v_size_1314_);
v___x_1317_ = lean_nat_dec_lt(v_size_1309_, v___x_1316_);
lean_dec(v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1345_; 
lean_inc(v_r_1313_);
lean_inc(v_l_1312_);
lean_inc(v_v_1311_);
lean_inc(v_k_1310_);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_l_1296_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1346_ = lean_ctor_get(v_l_1296_, 4);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_l_1296_, 3);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_l_1296_, 2);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_l_1296_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_l_1296_, 0);
lean_dec(v_unused_1350_);
v___x_1319_ = v_l_1296_;
v_isShared_1320_ = v_isSharedCheck_1345_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_l_1296_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1345_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1335_; 
v___x_1321_ = lean_nat_add(v___x_1291_, v_size_1292_);
lean_dec(v_size_1292_);
v___x_1322_ = lean_nat_add(v___x_1321_, v_size_1293_);
lean_dec(v_size_1293_);
if (lean_obj_tag(v_l_1312_) == 0)
{
lean_object* v_size_1343_; 
v_size_1343_ = lean_ctor_get(v_l_1312_, 0);
lean_inc(v_size_1343_);
v___y_1335_ = v_size_1343_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_unsigned_to_nat(0u);
v___y_1335_ = v___x_1344_;
goto v___jp_1334_;
}
v___jp_1323_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = lean_nat_add(v___y_1324_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec(v___y_1324_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 4, v_r_1297_);
lean_ctor_set(v___x_1319_, 3, v_r_1313_);
lean_ctor_set(v___x_1319_, 2, v_v_1295_);
lean_ctor_set(v___x_1319_, 1, v_k_1294_);
lean_ctor_set(v___x_1319_, 0, v___x_1327_);
v___x_1329_ = v___x_1319_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1294_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1295_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_r_1313_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_r_1297_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 4, v___x_1329_);
lean_ctor_set(v___x_1307_, 3, v___y_1325_);
lean_ctor_set(v___x_1307_, 2, v_v_1311_);
lean_ctor_set(v___x_1307_, 1, v_k_1310_);
lean_ctor_set(v___x_1307_, 0, v___x_1322_);
v___x_1331_ = v___x_1307_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1310_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1311_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v___y_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
v___jp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_nat_add(v___x_1321_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec(v___x_1321_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_l_1312_);
lean_ctor_set(v___x_1287_, 3, v_impl_1290_);
lean_ctor_set(v___x_1287_, 0, v___x_1336_);
v___x_1338_ = v___x_1287_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_impl_1290_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_l_1312_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_nat_add(v___x_1291_, v_size_1314_);
if (lean_obj_tag(v_r_1313_) == 0)
{
lean_object* v_size_1340_; 
v_size_1340_ = lean_ctor_get(v_r_1313_, 0);
lean_inc(v_size_1340_);
v___y_1324_ = v___x_1339_;
v___y_1325_ = v___x_1338_;
v___y_1326_ = v_size_1340_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v___y_1324_ = v___x_1339_;
v___y_1325_ = v___x_1338_;
v___y_1326_ = v___x_1341_;
goto v___jp_1323_;
}
}
}
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_del_object(v___x_1287_);
v___x_1351_ = lean_nat_add(v___x_1291_, v_size_1292_);
lean_dec(v_size_1292_);
v___x_1352_ = lean_nat_add(v___x_1351_, v_size_1293_);
lean_dec(v_size_1293_);
v___x_1353_ = lean_nat_add(v___x_1351_, v_size_1309_);
lean_dec(v___x_1351_);
lean_inc_ref(v_impl_1290_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 4, v_l_1296_);
lean_ctor_set(v___x_1307_, 3, v_impl_1290_);
lean_ctor_set(v___x_1307_, 2, v_v_1283_);
lean_ctor_set(v___x_1307_, 1, v_k_1282_);
lean_ctor_set(v___x_1307_, 0, v___x_1353_);
v___x_1355_ = v___x_1307_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_impl_1290_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_l_1296_);
v___x_1355_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v_impl_1290_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1363_ = lean_ctor_get(v_impl_1290_, 4);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_impl_1290_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_impl_1290_, 2);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_impl_1290_, 1);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_impl_1290_, 0);
lean_dec(v_unused_1367_);
v___x_1357_ = v_impl_1290_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v_impl_1290_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 4, v_r_1297_);
lean_ctor_set(v___x_1357_, 3, v___x_1355_);
lean_ctor_set(v___x_1357_, 2, v_v_1295_);
lean_ctor_set(v___x_1357_, 1, v_k_1294_);
lean_ctor_set(v___x_1357_, 0, v___x_1352_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1294_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1295_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_r_1297_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v_size_1375_ = lean_ctor_get(v_impl_1290_, 0);
lean_inc(v_size_1375_);
v___x_1376_ = lean_nat_add(v___x_1291_, v_size_1375_);
lean_dec(v_size_1375_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 3, v_impl_1290_);
lean_ctor_set(v___x_1287_, 0, v___x_1376_);
v___x_1378_ = v___x_1287_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_impl_1290_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_r_1285_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
if (lean_obj_tag(v_r_1285_) == 0)
{
lean_object* v_l_1380_; 
v_l_1380_ = lean_ctor_get(v_r_1285_, 3);
lean_inc(v_l_1380_);
if (lean_obj_tag(v_l_1380_) == 0)
{
lean_object* v_r_1381_; 
v_r_1381_ = lean_ctor_get(v_r_1285_, 4);
lean_inc(v_r_1381_);
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_size_1382_; lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
v_size_1382_ = lean_ctor_get(v_r_1285_, 0);
v_k_1383_ = lean_ctor_get(v_r_1285_, 1);
v_v_1384_ = lean_ctor_get(v_r_1285_, 2);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1398_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1399_);
v___x_1386_ = v_r_1285_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_v_1384_);
lean_inc(v_k_1383_);
lean_inc(v_size_1382_);
lean_dec(v_r_1285_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_size_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v_size_1388_ = lean_ctor_get(v_l_1380_, 0);
v___x_1389_ = lean_nat_add(v___x_1291_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1390_ = lean_nat_add(v___x_1291_, v_size_1388_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1380_);
lean_ctor_set(v___x_1386_, 3, v_impl_1290_);
lean_ctor_set(v___x_1386_, 2, v_v_1283_);
lean_ctor_set(v___x_1386_, 1, v_k_1282_);
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_impl_1290_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_l_1380_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_r_1381_);
lean_ctor_set(v___x_1287_, 3, v___x_1392_);
lean_ctor_set(v___x_1287_, 2, v_v_1384_);
lean_ctor_set(v___x_1287_, 1, v_k_1383_);
lean_ctor_set(v___x_1287_, 0, v___x_1389_);
v___x_1394_ = v___x_1287_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_r_1381_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1424_; 
v_k_1400_ = lean_ctor_get(v_r_1285_, 1);
v_v_1401_ = lean_ctor_get(v_r_1285_, 2);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; 
v_unused_1425_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1427_);
v___x_1403_ = v_r_1285_;
v_isShared_1404_ = v_isSharedCheck_1424_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
lean_dec(v_r_1285_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1424_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1420_; 
v_k_1405_ = lean_ctor_get(v_l_1380_, 1);
v_v_1406_ = lean_ctor_get(v_l_1380_, 2);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; lean_object* v_unused_1422_; lean_object* v_unused_1423_; 
v_unused_1421_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1423_);
v___x_1408_ = v_l_1380_;
v_isShared_1409_ = v_isSharedCheck_1420_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_v_1406_);
lean_inc(v_k_1405_);
lean_dec(v_l_1380_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1420_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = lean_unsigned_to_nat(3u);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 4, v_r_1381_);
lean_ctor_set(v___x_1408_, 3, v_r_1381_);
lean_ctor_set(v___x_1408_, 2, v_v_1283_);
lean_ctor_set(v___x_1408_, 1, v_k_1282_);
lean_ctor_set(v___x_1408_, 0, v___x_1291_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_r_1381_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_r_1381_);
v___x_1412_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 3, v_r_1381_);
lean_ctor_set(v___x_1403_, 0, v___x_1291_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1400_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1401_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_r_1381_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_r_1381_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1414_);
lean_ctor_set(v___x_1287_, 3, v___x_1412_);
lean_ctor_set(v___x_1287_, 2, v_v_1406_);
lean_ctor_set(v___x_1287_, 1, v_k_1405_);
lean_ctor_set(v___x_1287_, 0, v___x_1410_);
v___x_1416_ = v___x_1287_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1428_; 
v_r_1428_ = lean_ctor_get(v_r_1285_, 4);
lean_inc(v_r_1428_);
if (lean_obj_tag(v_r_1428_) == 0)
{
lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1441_; 
v_k_1429_ = lean_ctor_get(v_r_1285_, 1);
v_v_1430_ = lean_ctor_get(v_r_1285_, 2);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; 
v_unused_1442_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1444_);
v___x_1432_ = v_r_1285_;
v_isShared_1433_ = v_isSharedCheck_1441_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
lean_dec(v_r_1285_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1441_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(3u);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 4, v_l_1380_);
lean_ctor_set(v___x_1432_, 2, v_v_1283_);
lean_ctor_set(v___x_1432_, 1, v_k_1282_);
lean_ctor_set(v___x_1432_, 0, v___x_1291_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_l_1380_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_r_1428_);
lean_ctor_set(v___x_1287_, 3, v___x_1436_);
lean_ctor_set(v___x_1287_, 2, v_v_1430_);
lean_ctor_set(v___x_1287_, 1, v_k_1429_);
lean_ctor_set(v___x_1287_, 0, v___x_1434_);
v___x_1438_ = v___x_1287_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_r_1428_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1458_; 
v_size_1445_ = lean_ctor_get(v_r_1285_, 0);
v_k_1446_ = lean_ctor_get(v_r_1285_, 1);
v_v_1447_ = lean_ctor_get(v_r_1285_, 2);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1459_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1460_);
v___x_1449_ = v_r_1285_;
v_isShared_1450_ = v_isSharedCheck_1458_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_v_1447_);
lean_inc(v_k_1446_);
lean_inc(v_size_1445_);
lean_dec(v_r_1285_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1458_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 3, v_r_1428_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_size_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1447_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_r_1428_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_r_1428_);
v___x_1452_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_unsigned_to_nat(2u);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1452_);
lean_ctor_set(v___x_1287_, 3, v_r_1428_);
lean_ctor_set(v___x_1287_, 0, v___x_1453_);
v___x_1455_ = v___x_1287_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_r_1428_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v___x_1452_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
else
{
lean_object* v___x_1462_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 3, v_r_1285_);
lean_ctor_set(v___x_1287_, 0, v___x_1291_);
v___x_1462_ = v___x_1287_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_r_1285_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_r_1285_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1287_);
lean_dec(v_v_1283_);
lean_dec(v_k_1282_);
if (lean_obj_tag(v_l_1284_) == 0)
{
if (lean_obj_tag(v_r_1285_) == 0)
{
lean_object* v_size_1464_; lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v_l_1467_; lean_object* v_r_1468_; lean_object* v_size_1469_; lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v_l_1472_; lean_object* v_r_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v_size_1464_ = lean_ctor_get(v_l_1284_, 0);
v_k_1465_ = lean_ctor_get(v_l_1284_, 1);
v_v_1466_ = lean_ctor_get(v_l_1284_, 2);
v_l_1467_ = lean_ctor_get(v_l_1284_, 3);
v_r_1468_ = lean_ctor_get(v_l_1284_, 4);
lean_inc(v_r_1468_);
v_size_1469_ = lean_ctor_get(v_r_1285_, 0);
v_k_1470_ = lean_ctor_get(v_r_1285_, 1);
v_v_1471_ = lean_ctor_get(v_r_1285_, 2);
v_l_1472_ = lean_ctor_get(v_r_1285_, 3);
lean_inc(v_l_1472_);
v_r_1473_ = lean_ctor_get(v_r_1285_, 4);
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = lean_nat_dec_lt(v_size_1464_, v_size_1469_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1611_; 
lean_inc(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1612_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1284_, 2);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_l_1284_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1616_);
v___x_1477_ = v_l_1284_;
v_isShared_1478_ = v_isSharedCheck_1611_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_l_1284_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1611_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v_tree_1480_; 
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1465_, v_v_1466_, v_l_1467_, v_r_1468_);
v_tree_1480_ = lean_ctor_get(v___x_1479_, 2);
lean_inc(v_tree_1480_);
if (lean_obj_tag(v_tree_1480_) == 0)
{
lean_object* v_k_1481_; lean_object* v_v_1482_; lean_object* v_size_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_k_1481_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_k_1481_);
v_v_1482_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_v_1482_);
lean_dec_ref(v___x_1479_);
v_size_1483_ = lean_ctor_get(v_tree_1480_, 0);
v___x_1484_ = lean_unsigned_to_nat(3u);
v___x_1485_ = lean_nat_mul(v___x_1484_, v_size_1483_);
v___x_1486_ = lean_nat_dec_lt(v___x_1485_, v_size_1469_);
lean_dec(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_dec(v_l_1472_);
v___x_1487_ = lean_nat_add(v___x_1474_, v_size_1483_);
v___x_1488_ = lean_nat_add(v___x_1487_, v_size_1469_);
lean_dec(v___x_1487_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_r_1285_);
lean_ctor_set(v___x_1477_, 3, v_tree_1480_);
lean_ctor_set(v___x_1477_, 2, v_v_1482_);
lean_ctor_set(v___x_1477_, 1, v_k_1481_);
lean_ctor_set(v___x_1477_, 0, v___x_1488_);
v___x_1490_ = v___x_1477_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_tree_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1285_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
else
{
lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1546_; 
lean_inc(v_r_1473_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
lean_inc(v_size_1469_);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; 
v_unused_1547_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1285_, 2);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_r_1285_, 1);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1551_);
v___x_1493_ = v_r_1285_;
v_isShared_1494_ = v_isSharedCheck_1546_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v_r_1285_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1546_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_size_1495_; lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v_l_1498_; lean_object* v_r_1499_; lean_object* v_size_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_size_1495_ = lean_ctor_get(v_l_1472_, 0);
v_k_1496_ = lean_ctor_get(v_l_1472_, 1);
v_v_1497_ = lean_ctor_get(v_l_1472_, 2);
v_l_1498_ = lean_ctor_get(v_l_1472_, 3);
v_r_1499_ = lean_ctor_get(v_l_1472_, 4);
v_size_1500_ = lean_ctor_get(v_r_1473_, 0);
v___x_1501_ = lean_unsigned_to_nat(2u);
v___x_1502_ = lean_nat_mul(v___x_1501_, v_size_1500_);
v___x_1503_ = lean_nat_dec_lt(v_size_1495_, v___x_1502_);
lean_dec(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1531_; 
lean_inc(v_r_1499_);
lean_inc(v_l_1498_);
lean_inc(v_v_1497_);
lean_inc(v_k_1496_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_l_1472_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1532_ = lean_ctor_get(v_l_1472_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1472_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1472_, 2);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1472_, 1);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1472_, 0);
lean_dec(v_unused_1536_);
v___x_1505_ = v_l_1472_;
v_isShared_1506_ = v_isSharedCheck_1531_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_l_1472_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1531_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1521_; 
v___x_1507_ = lean_nat_add(v___x_1474_, v_size_1483_);
v___x_1508_ = lean_nat_add(v___x_1507_, v_size_1469_);
lean_dec(v_size_1469_);
if (lean_obj_tag(v_l_1498_) == 0)
{
lean_object* v_size_1529_; 
v_size_1529_ = lean_ctor_get(v_l_1498_, 0);
lean_inc(v_size_1529_);
v___y_1521_ = v_size_1529_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_unsigned_to_nat(0u);
v___y_1521_ = v___x_1530_;
goto v___jp_1520_;
}
v___jp_1509_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_nat_add(v___y_1510_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec(v___y_1510_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_r_1473_);
lean_ctor_set(v___x_1505_, 3, v_r_1499_);
lean_ctor_set(v___x_1505_, 2, v_v_1471_);
lean_ctor_set(v___x_1505_, 1, v_k_1470_);
lean_ctor_set(v___x_1505_, 0, v___x_1513_);
v___x_1515_ = v___x_1505_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_r_1499_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_r_1473_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v___x_1515_);
lean_ctor_set(v___x_1493_, 3, v___y_1511_);
lean_ctor_set(v___x_1493_, 2, v_v_1497_);
lean_ctor_set(v___x_1493_, 1, v_k_1496_);
lean_ctor_set(v___x_1493_, 0, v___x_1508_);
v___x_1517_ = v___x_1493_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1496_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1497_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___y_1511_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_nat_add(v___x_1507_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec(v___x_1507_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_l_1498_);
lean_ctor_set(v___x_1477_, 3, v_tree_1480_);
lean_ctor_set(v___x_1477_, 2, v_v_1482_);
lean_ctor_set(v___x_1477_, 1, v_k_1481_);
lean_ctor_set(v___x_1477_, 0, v___x_1522_);
v___x_1524_ = v___x_1477_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_tree_1480_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_l_1498_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_nat_add(v___x_1474_, v_size_1500_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_size_1526_; 
v_size_1526_ = lean_ctor_get(v_r_1499_, 0);
lean_inc(v_size_1526_);
v___y_1510_ = v___x_1525_;
v___y_1511_ = v___x_1524_;
v___y_1512_ = v_size_1526_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___y_1510_ = v___x_1525_;
v___y_1511_ = v___x_1524_;
v___y_1512_ = v___x_1527_;
goto v___jp_1509_;
}
}
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1537_ = lean_nat_add(v___x_1474_, v_size_1483_);
v___x_1538_ = lean_nat_add(v___x_1537_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1539_ = lean_nat_add(v___x_1537_, v_size_1495_);
lean_dec(v___x_1537_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_l_1472_);
lean_ctor_set(v___x_1493_, 3, v_tree_1480_);
lean_ctor_set(v___x_1493_, 2, v_v_1482_);
lean_ctor_set(v___x_1493_, 1, v_k_1481_);
lean_ctor_set(v___x_1493_, 0, v___x_1539_);
v___x_1541_ = v___x_1493_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1481_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1482_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_tree_1480_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_l_1472_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_r_1473_);
lean_ctor_set(v___x_1477_, 3, v___x_1541_);
lean_ctor_set(v___x_1477_, 2, v_v_1471_);
lean_ctor_set(v___x_1477_, 1, v_k_1470_);
lean_ctor_set(v___x_1477_, 0, v___x_1538_);
v___x_1543_ = v___x_1477_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_r_1473_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
else
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1605_; 
lean_inc(v_r_1473_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
lean_inc(v_size_1469_);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1285_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_r_1285_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1610_);
v___x_1553_ = v_r_1285_;
v_isShared_1554_ = v_isSharedCheck_1605_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v_r_1285_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1605_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
if (lean_obj_tag(v_l_1472_) == 0)
{
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v_k_1555_; lean_object* v_v_1556_; lean_object* v_size_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v_k_1555_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_k_1555_);
v_v_1556_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_v_1556_);
lean_dec_ref(v___x_1479_);
v_size_1557_ = lean_ctor_get(v_l_1472_, 0);
v___x_1558_ = lean_nat_add(v___x_1474_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1559_ = lean_nat_add(v___x_1474_, v_size_1557_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_l_1472_);
lean_ctor_set(v___x_1553_, 3, v_tree_1480_);
lean_ctor_set(v___x_1553_, 2, v_v_1556_);
lean_ctor_set(v___x_1553_, 1, v_k_1555_);
lean_ctor_set(v___x_1553_, 0, v___x_1559_);
v___x_1561_ = v___x_1553_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1555_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1556_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_tree_1480_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_l_1472_);
v___x_1561_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_r_1473_);
lean_ctor_set(v___x_1477_, 3, v___x_1561_);
lean_ctor_set(v___x_1477_, 2, v_v_1471_);
lean_ctor_set(v___x_1477_, 1, v_k_1470_);
lean_ctor_set(v___x_1477_, 0, v___x_1558_);
v___x_1563_ = v___x_1477_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_r_1473_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_size_1469_);
v_k_1566_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_k_1566_);
v_v_1567_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_v_1567_);
lean_dec_ref(v___x_1479_);
v_k_1568_ = lean_ctor_get(v_l_1472_, 1);
v_v_1569_ = lean_ctor_get(v_l_1472_, 2);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_l_1472_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; lean_object* v_unused_1585_; lean_object* v_unused_1586_; 
v_unused_1584_ = lean_ctor_get(v_l_1472_, 4);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_l_1472_, 3);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_l_1472_, 0);
lean_dec(v_unused_1586_);
v___x_1571_ = v_l_1472_;
v_isShared_1572_ = v_isSharedCheck_1583_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_v_1569_);
lean_inc(v_k_1568_);
lean_dec(v_l_1472_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1583_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_unsigned_to_nat(3u);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v_r_1473_);
lean_ctor_set(v___x_1571_, 3, v_r_1473_);
lean_ctor_set(v___x_1571_, 2, v_v_1567_);
lean_ctor_set(v___x_1571_, 1, v_k_1566_);
lean_ctor_set(v___x_1571_, 0, v___x_1474_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_r_1473_);
v___x_1575_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v_r_1473_);
lean_ctor_set(v___x_1553_, 0, v___x_1474_);
v___x_1577_ = v___x_1553_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_r_1473_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v___x_1577_);
lean_ctor_set(v___x_1477_, 3, v___x_1575_);
lean_ctor_set(v___x_1477_, 2, v_v_1569_);
lean_ctor_set(v___x_1477_, 1, v_k_1568_);
lean_ctor_set(v___x_1477_, 0, v___x_1573_);
v___x_1579_ = v___x_1477_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1568_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1569_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec(v_size_1469_);
v_k_1587_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_k_1587_);
v_v_1588_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_v_1588_);
lean_dec_ref(v___x_1479_);
v___x_1589_ = lean_unsigned_to_nat(3u);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_l_1472_);
lean_ctor_set(v___x_1553_, 2, v_v_1588_);
lean_ctor_set(v___x_1553_, 1, v_k_1587_);
lean_ctor_set(v___x_1553_, 0, v___x_1474_);
v___x_1591_ = v___x_1553_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1472_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_l_1472_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_r_1473_);
lean_ctor_set(v___x_1477_, 3, v___x_1591_);
lean_ctor_set(v___x_1477_, 2, v_v_1471_);
lean_ctor_set(v___x_1477_, 1, v_k_1470_);
lean_ctor_set(v___x_1477_, 0, v___x_1589_);
v___x_1593_ = v___x_1477_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_r_1473_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
else
{
lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v___x_1599_; 
v_k_1596_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_k_1596_);
v_v_1597_ = lean_ctor_get(v___x_1479_, 1);
lean_inc(v_v_1597_);
lean_dec_ref(v___x_1479_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v_r_1473_);
v___x_1599_ = v___x_1553_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_size_1469_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1473_);
v___x_1599_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(2u);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v___x_1599_);
lean_ctor_set(v___x_1477_, 3, v_r_1473_);
lean_ctor_set(v___x_1477_, 2, v_v_1597_);
lean_ctor_set(v___x_1477_, 1, v_k_1596_);
lean_ctor_set(v___x_1477_, 0, v___x_1600_);
v___x_1602_ = v___x_1477_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1596_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_r_1473_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v___x_1599_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
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
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1769_; 
lean_inc(v_r_1473_);
lean_inc(v_v_1471_);
lean_inc(v_k_1470_);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_r_1285_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; 
v_unused_1770_ = lean_ctor_get(v_r_1285_, 4);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_r_1285_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_r_1285_, 2);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_r_1285_, 1);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_r_1285_, 0);
lean_dec(v_unused_1774_);
v___x_1618_ = v_r_1285_;
v_isShared_1619_ = v_isSharedCheck_1769_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_r_1285_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1769_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v_tree_1621_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1470_, v_v_1471_, v_l_1472_, v_r_1473_);
v_tree_1621_ = lean_ctor_get(v___x_1620_, 2);
lean_inc(v_tree_1621_);
if (lean_obj_tag(v_tree_1621_) == 0)
{
lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v_size_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_k_1622_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_k_1622_);
v_v_1623_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_v_1623_);
lean_dec_ref(v___x_1620_);
v_size_1624_ = lean_ctor_get(v_tree_1621_, 0);
v___x_1625_ = lean_unsigned_to_nat(3u);
v___x_1626_ = lean_nat_mul(v___x_1625_, v_size_1624_);
v___x_1627_ = lean_nat_dec_lt(v___x_1626_, v_size_1464_);
lean_dec(v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec(v_r_1468_);
v___x_1628_ = lean_nat_add(v___x_1474_, v_size_1464_);
v___x_1629_ = lean_nat_add(v___x_1628_, v_size_1624_);
lean_dec(v___x_1628_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_tree_1621_);
lean_ctor_set(v___x_1618_, 3, v_l_1284_);
lean_ctor_set(v___x_1618_, 2, v_v_1623_);
lean_ctor_set(v___x_1618_, 1, v_k_1622_);
lean_ctor_set(v___x_1618_, 0, v___x_1629_);
v___x_1631_ = v___x_1618_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v_tree_1621_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1698_; 
lean_inc(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
lean_inc(v_size_1464_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1699_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_l_1284_, 2);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_l_1284_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1703_);
v___x_1634_ = v_l_1284_;
v_isShared_1635_ = v_isSharedCheck_1698_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v_l_1284_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1698_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_size_1636_; lean_object* v_size_1637_; lean_object* v_k_1638_; lean_object* v_v_1639_; lean_object* v_l_1640_; lean_object* v_r_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v_size_1636_ = lean_ctor_get(v_l_1467_, 0);
v_size_1637_ = lean_ctor_get(v_r_1468_, 0);
v_k_1638_ = lean_ctor_get(v_r_1468_, 1);
v_v_1639_ = lean_ctor_get(v_r_1468_, 2);
v_l_1640_ = lean_ctor_get(v_r_1468_, 3);
v_r_1641_ = lean_ctor_get(v_r_1468_, 4);
v___x_1642_ = lean_unsigned_to_nat(2u);
v___x_1643_ = lean_nat_mul(v___x_1642_, v_size_1636_);
v___x_1644_ = lean_nat_dec_lt(v_size_1637_, v___x_1643_);
lean_dec(v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_r_1641_);
lean_inc(v_l_1640_);
lean_inc(v_v_1639_);
lean_inc(v_k_1638_);
lean_del_object(v___x_1634_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_r_1468_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1683_ = lean_ctor_get(v_r_1468_, 4);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_r_1468_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_r_1468_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_r_1468_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_r_1468_, 0);
lean_dec(v_unused_1687_);
v___x_1646_ = v_r_1468_;
v_isShared_1647_ = v_isSharedCheck_1682_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v_r_1468_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1682_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___x_1670_; lean_object* v___y_1672_; 
v___x_1648_ = lean_nat_add(v___x_1474_, v_size_1464_);
lean_dec(v_size_1464_);
v___x_1649_ = lean_nat_add(v___x_1648_, v_size_1624_);
lean_dec(v___x_1648_);
v___x_1670_ = lean_nat_add(v___x_1474_, v_size_1636_);
if (lean_obj_tag(v_l_1640_) == 0)
{
lean_object* v_size_1680_; 
v_size_1680_ = lean_ctor_get(v_l_1640_, 0);
lean_inc(v_size_1680_);
v___y_1672_ = v_size_1680_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___y_1672_ = v___x_1681_;
goto v___jp_1671_;
}
v___jp_1650_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_nat_add(v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec(v___y_1652_);
lean_inc_ref(v_tree_1621_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 4, v_tree_1621_);
lean_ctor_set(v___x_1646_, 3, v_r_1641_);
lean_ctor_set(v___x_1646_, 2, v_v_1623_);
lean_ctor_set(v___x_1646_, 1, v_k_1622_);
lean_ctor_set(v___x_1646_, 0, v___x_1654_);
v___x_1656_ = v___x_1646_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_r_1641_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_tree_1621_);
v___x_1656_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v_tree_1621_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; lean_object* v_unused_1668_; 
v_unused_1664_ = lean_ctor_get(v_tree_1621_, 4);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_tree_1621_, 3);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_tree_1621_, 2);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_tree_1621_, 1);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_tree_1621_, 0);
lean_dec(v_unused_1668_);
v___x_1658_ = v_tree_1621_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_dec(v_tree_1621_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v___x_1656_);
lean_ctor_set(v___x_1658_, 3, v___y_1651_);
lean_ctor_set(v___x_1658_, 2, v_v_1639_);
lean_ctor_set(v___x_1658_, 1, v_k_1638_);
lean_ctor_set(v___x_1658_, 0, v___x_1649_);
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1638_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1639_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v___y_1651_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v___x_1656_);
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
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_nat_add(v___x_1670_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec(v___x_1670_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_l_1640_);
lean_ctor_set(v___x_1618_, 3, v_l_1467_);
lean_ctor_set(v___x_1618_, 2, v_v_1466_);
lean_ctor_set(v___x_1618_, 1, v_k_1465_);
lean_ctor_set(v___x_1618_, 0, v___x_1673_);
v___x_1675_ = v___x_1618_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v_l_1640_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_nat_add(v___x_1474_, v_size_1624_);
if (lean_obj_tag(v_r_1641_) == 0)
{
lean_object* v_size_1677_; 
v_size_1677_ = lean_ctor_get(v_r_1641_, 0);
lean_inc(v_size_1677_);
v___y_1651_ = v___x_1675_;
v___y_1652_ = v___x_1676_;
v___y_1653_ = v_size_1677_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___y_1651_ = v___x_1675_;
v___y_1652_ = v___x_1676_;
v___y_1653_ = v___x_1678_;
goto v___jp_1650_;
}
}
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1688_ = lean_nat_add(v___x_1474_, v_size_1464_);
lean_dec(v_size_1464_);
v___x_1689_ = lean_nat_add(v___x_1688_, v_size_1624_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_nat_add(v___x_1474_, v_size_1624_);
v___x_1691_ = lean_nat_add(v___x_1690_, v_size_1637_);
lean_dec(v___x_1690_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_tree_1621_);
lean_ctor_set(v___x_1618_, 3, v_r_1468_);
lean_ctor_set(v___x_1618_, 2, v_v_1623_);
lean_ctor_set(v___x_1618_, 1, v_k_1622_);
lean_ctor_set(v___x_1618_, 0, v___x_1691_);
v___x_1693_ = v___x_1618_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_r_1468_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_tree_1621_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 4, v___x_1693_);
lean_ctor_set(v___x_1634_, 0, v___x_1689_);
v___x_1695_ = v___x_1634_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1696_, 4, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1467_) == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
lean_inc(v_size_1464_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; lean_object* v_unused_1729_; lean_object* v_unused_1730_; lean_object* v_unused_1731_; lean_object* v_unused_1732_; 
v_unused_1728_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_l_1284_, 2);
lean_dec(v_unused_1730_);
v_unused_1731_ = lean_ctor_get(v_l_1284_, 1);
lean_dec(v_unused_1731_);
v_unused_1732_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1732_);
v___x_1705_ = v_l_1284_;
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_l_1284_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
if (lean_obj_tag(v_r_1468_) == 0)
{
lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_size_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v_k_1707_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_k_1707_);
v_v_1708_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_v_1708_);
lean_dec_ref(v___x_1620_);
v_size_1709_ = lean_ctor_get(v_r_1468_, 0);
v___x_1710_ = lean_nat_add(v___x_1474_, v_size_1464_);
lean_dec(v_size_1464_);
v___x_1711_ = lean_nat_add(v___x_1474_, v_size_1709_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_tree_1621_);
lean_ctor_set(v___x_1618_, 3, v_r_1468_);
lean_ctor_set(v___x_1618_, 2, v_v_1708_);
lean_ctor_set(v___x_1618_, 1, v_k_1707_);
lean_ctor_set(v___x_1618_, 0, v___x_1711_);
v___x_1713_ = v___x_1618_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_r_1468_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_tree_1621_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 4, v___x_1713_);
lean_ctor_set(v___x_1705_, 0, v___x_1710_);
v___x_1715_ = v___x_1705_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_k_1718_; lean_object* v_v_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec(v_size_1464_);
v_k_1718_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_k_1718_);
v_v_1719_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_v_1719_);
lean_dec_ref(v___x_1620_);
v___x_1720_ = lean_unsigned_to_nat(3u);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_r_1468_);
lean_ctor_set(v___x_1618_, 3, v_r_1468_);
lean_ctor_set(v___x_1618_, 2, v_v_1719_);
lean_ctor_set(v___x_1618_, 1, v_k_1718_);
lean_ctor_set(v___x_1618_, 0, v___x_1474_);
v___x_1722_ = v___x_1618_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_r_1468_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_r_1468_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 4, v___x_1722_);
lean_ctor_set(v___x_1705_, 0, v___x_1720_);
v___x_1724_ = v___x_1705_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1468_) == 0)
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1757_; 
lean_inc(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; 
v_unused_1758_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_l_1284_, 2);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_l_1284_, 1);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1762_);
v___x_1734_ = v_l_1284_;
v_isShared_1735_ = v_isSharedCheck_1757_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v_l_1284_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1757_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_k_1736_; lean_object* v_v_1737_; lean_object* v_k_1738_; lean_object* v_v_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1753_; 
v_k_1736_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_k_1736_);
v_v_1737_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_v_1737_);
lean_dec_ref(v___x_1620_);
v_k_1738_ = lean_ctor_get(v_r_1468_, 1);
v_v_1739_ = lean_ctor_get(v_r_1468_, 2);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_r_1468_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; 
v_unused_1754_ = lean_ctor_get(v_r_1468_, 4);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_r_1468_, 3);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_r_1468_, 0);
lean_dec(v_unused_1756_);
v___x_1741_ = v_r_1468_;
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_v_1739_);
lean_inc(v_k_1738_);
lean_dec(v_r_1468_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1753_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_unsigned_to_nat(3u);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 4, v_l_1467_);
lean_ctor_set(v___x_1741_, 3, v_l_1467_);
lean_ctor_set(v___x_1741_, 2, v_v_1466_);
lean_ctor_set(v___x_1741_, 1, v_k_1465_);
lean_ctor_set(v___x_1741_, 0, v___x_1474_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_l_1467_);
v___x_1745_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_l_1467_);
lean_ctor_set(v___x_1618_, 3, v_l_1467_);
lean_ctor_set(v___x_1618_, 2, v_v_1737_);
lean_ctor_set(v___x_1618_, 1, v_k_1736_);
lean_ctor_set(v___x_1618_, 0, v___x_1474_);
v___x_1747_ = v___x_1618_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_k_1736_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_v_1737_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_l_1467_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_l_1467_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 4, v___x_1747_);
lean_ctor_set(v___x_1734_, 3, v___x_1745_);
lean_ctor_set(v___x_1734_, 2, v_v_1739_);
lean_ctor_set(v___x_1734_, 1, v_k_1738_);
lean_ctor_set(v___x_1734_, 0, v___x_1743_);
v___x_1749_ = v___x_1734_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_k_1738_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_v_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
else
{
lean_object* v_k_1763_; lean_object* v_v_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_k_1763_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_k_1763_);
v_v_1764_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_v_1764_);
lean_dec_ref(v___x_1620_);
v___x_1765_ = lean_unsigned_to_nat(2u);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v_r_1468_);
lean_ctor_set(v___x_1618_, 3, v_l_1284_);
lean_ctor_set(v___x_1618_, 2, v_v_1764_);
lean_ctor_set(v___x_1618_, 1, v_k_1763_);
lean_ctor_set(v___x_1618_, 0, v___x_1765_);
v___x_1767_ = v___x_1618_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1763_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1764_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_r_1468_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
else
{
return v_l_1284_;
}
}
else
{
return v_r_1285_;
}
}
default: 
{
lean_object* v_impl_1775_; lean_object* v___x_1776_; 
v_impl_1775_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1280_, v_r_1285_);
v___x_1776_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1775_) == 0)
{
if (lean_obj_tag(v_l_1284_) == 0)
{
lean_object* v_size_1777_; lean_object* v_size_1778_; lean_object* v_k_1779_; lean_object* v_v_1780_; lean_object* v_l_1781_; lean_object* v_r_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_size_1777_ = lean_ctor_get(v_impl_1775_, 0);
lean_inc(v_size_1777_);
v_size_1778_ = lean_ctor_get(v_l_1284_, 0);
v_k_1779_ = lean_ctor_get(v_l_1284_, 1);
v_v_1780_ = lean_ctor_get(v_l_1284_, 2);
v_l_1781_ = lean_ctor_get(v_l_1284_, 3);
v_r_1782_ = lean_ctor_get(v_l_1284_, 4);
lean_inc(v_r_1782_);
v___x_1783_ = lean_unsigned_to_nat(3u);
v___x_1784_ = lean_nat_mul(v___x_1783_, v_size_1777_);
v___x_1785_ = lean_nat_dec_lt(v___x_1784_, v_size_1778_);
lean_dec(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
lean_dec(v_r_1782_);
v___x_1786_ = lean_nat_add(v___x_1776_, v_size_1778_);
v___x_1787_ = lean_nat_add(v___x_1786_, v_size_1777_);
lean_dec(v_size_1777_);
lean_dec(v___x_1786_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_impl_1775_);
lean_ctor_set(v___x_1287_, 0, v___x_1787_);
v___x_1789_ = v___x_1287_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_impl_1775_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
else
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_l_1781_);
lean_inc(v_v_1780_);
lean_inc(v_k_1779_);
lean_inc(v_size_1778_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; 
v_unused_1857_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_l_1284_, 2);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_l_1284_, 1);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1861_);
v___x_1792_ = v_l_1284_;
v_isShared_1793_ = v_isSharedCheck_1856_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_l_1284_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1856_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_size_1794_; lean_object* v_size_1795_; lean_object* v_k_1796_; lean_object* v_v_1797_; lean_object* v_l_1798_; lean_object* v_r_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_size_1794_ = lean_ctor_get(v_l_1781_, 0);
v_size_1795_ = lean_ctor_get(v_r_1782_, 0);
v_k_1796_ = lean_ctor_get(v_r_1782_, 1);
v_v_1797_ = lean_ctor_get(v_r_1782_, 2);
v_l_1798_ = lean_ctor_get(v_r_1782_, 3);
v_r_1799_ = lean_ctor_get(v_r_1782_, 4);
v___x_1800_ = lean_unsigned_to_nat(2u);
v___x_1801_ = lean_nat_mul(v___x_1800_, v_size_1794_);
v___x_1802_ = lean_nat_dec_lt(v_size_1795_, v___x_1801_);
lean_dec(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1831_; 
lean_inc(v_r_1799_);
lean_inc(v_l_1798_);
lean_inc(v_v_1797_);
lean_inc(v_k_1796_);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_r_1782_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; lean_object* v_unused_1835_; lean_object* v_unused_1836_; 
v_unused_1832_ = lean_ctor_get(v_r_1782_, 4);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_r_1782_, 3);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_r_1782_, 2);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_r_1782_, 1);
lean_dec(v_unused_1835_);
v_unused_1836_ = lean_ctor_get(v_r_1782_, 0);
lean_dec(v_unused_1836_);
v___x_1804_ = v_r_1782_;
v_isShared_1805_ = v_isSharedCheck_1831_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v_r_1782_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1831_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___x_1819_; lean_object* v___y_1821_; 
v___x_1806_ = lean_nat_add(v___x_1776_, v_size_1778_);
lean_dec(v_size_1778_);
v___x_1807_ = lean_nat_add(v___x_1806_, v_size_1777_);
lean_dec(v___x_1806_);
v___x_1819_ = lean_nat_add(v___x_1776_, v_size_1794_);
if (lean_obj_tag(v_l_1798_) == 0)
{
lean_object* v_size_1829_; 
v_size_1829_ = lean_ctor_get(v_l_1798_, 0);
lean_inc(v_size_1829_);
v___y_1821_ = v_size_1829_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v___y_1821_ = v___x_1830_;
goto v___jp_1820_;
}
v___jp_1808_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_nat_add(v___y_1809_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec(v___y_1809_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 4, v_impl_1775_);
lean_ctor_set(v___x_1804_, 3, v_r_1799_);
lean_ctor_set(v___x_1804_, 2, v_v_1283_);
lean_ctor_set(v___x_1804_, 1, v_k_1282_);
lean_ctor_set(v___x_1804_, 0, v___x_1812_);
v___x_1814_ = v___x_1804_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_r_1799_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_impl_1775_);
v___x_1814_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 4, v___x_1814_);
lean_ctor_set(v___x_1792_, 3, v___y_1810_);
lean_ctor_set(v___x_1792_, 2, v_v_1797_);
lean_ctor_set(v___x_1792_, 1, v_k_1796_);
lean_ctor_set(v___x_1792_, 0, v___x_1807_);
v___x_1816_ = v___x_1792_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_k_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_v_1797_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v___y_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_nat_add(v___x_1819_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec(v___x_1819_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_l_1798_);
lean_ctor_set(v___x_1287_, 3, v_l_1781_);
lean_ctor_set(v___x_1287_, 2, v_v_1780_);
lean_ctor_set(v___x_1287_, 1, v_k_1779_);
lean_ctor_set(v___x_1287_, 0, v___x_1822_);
v___x_1824_ = v___x_1287_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_k_1779_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_v_1780_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_l_1781_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_l_1798_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_nat_add(v___x_1776_, v_size_1777_);
lean_dec(v_size_1777_);
if (lean_obj_tag(v_r_1799_) == 0)
{
lean_object* v_size_1826_; 
v_size_1826_ = lean_ctor_get(v_r_1799_, 0);
lean_inc(v_size_1826_);
v___y_1809_ = v___x_1825_;
v___y_1810_ = v___x_1824_;
v___y_1811_ = v_size_1826_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_unsigned_to_nat(0u);
v___y_1809_ = v___x_1825_;
v___y_1810_ = v___x_1824_;
v___y_1811_ = v___x_1827_;
goto v___jp_1808_;
}
}
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_del_object(v___x_1287_);
v___x_1837_ = lean_nat_add(v___x_1776_, v_size_1778_);
lean_dec(v_size_1778_);
v___x_1838_ = lean_nat_add(v___x_1837_, v_size_1777_);
lean_dec(v___x_1837_);
v___x_1839_ = lean_nat_add(v___x_1776_, v_size_1777_);
lean_dec(v_size_1777_);
v___x_1840_ = lean_nat_add(v___x_1839_, v_size_1795_);
lean_dec(v___x_1839_);
lean_inc_ref(v_impl_1775_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 4, v_impl_1775_);
lean_ctor_set(v___x_1792_, 3, v_r_1782_);
lean_ctor_set(v___x_1792_, 2, v_v_1283_);
lean_ctor_set(v___x_1792_, 1, v_k_1282_);
lean_ctor_set(v___x_1792_, 0, v___x_1840_);
v___x_1842_ = v___x_1792_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_r_1782_);
lean_ctor_set(v_reuseFailAlloc_1855_, 4, v_impl_1775_);
v___x_1842_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_isSharedCheck_1849_ = !lean_is_exclusive(v_impl_1775_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1850_ = lean_ctor_get(v_impl_1775_, 4);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_impl_1775_, 3);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_impl_1775_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_impl_1775_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_impl_1775_, 0);
lean_dec(v_unused_1854_);
v___x_1844_ = v_impl_1775_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v_impl_1775_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 4, v___x_1842_);
lean_ctor_set(v___x_1844_, 3, v_l_1781_);
lean_ctor_set(v___x_1844_, 2, v_v_1780_);
lean_ctor_set(v___x_1844_, 1, v_k_1779_);
lean_ctor_set(v___x_1844_, 0, v___x_1838_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_k_1779_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_v_1780_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_l_1781_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v___x_1842_);
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
}
}
else
{
lean_object* v_size_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v_size_1862_ = lean_ctor_get(v_impl_1775_, 0);
lean_inc(v_size_1862_);
v___x_1863_ = lean_nat_add(v___x_1776_, v_size_1862_);
lean_dec(v_size_1862_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_impl_1775_);
lean_ctor_set(v___x_1287_, 0, v___x_1863_);
v___x_1865_ = v___x_1287_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_impl_1775_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
if (lean_obj_tag(v_l_1284_) == 0)
{
lean_object* v_l_1867_; 
v_l_1867_ = lean_ctor_get(v_l_1284_, 3);
if (lean_obj_tag(v_l_1867_) == 0)
{
lean_object* v_r_1868_; 
lean_inc_ref(v_l_1867_);
v_r_1868_ = lean_ctor_get(v_l_1284_, 4);
lean_inc(v_r_1868_);
if (lean_obj_tag(v_r_1868_) == 0)
{
lean_object* v_size_1869_; lean_object* v_k_1870_; lean_object* v_v_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1884_; 
v_size_1869_ = lean_ctor_get(v_l_1284_, 0);
v_k_1870_ = lean_ctor_get(v_l_1284_, 1);
v_v_1871_ = lean_ctor_get(v_l_1284_, 2);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1885_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1886_);
v___x_1873_ = v_l_1284_;
v_isShared_1874_ = v_isSharedCheck_1884_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_v_1871_);
lean_inc(v_k_1870_);
lean_inc(v_size_1869_);
lean_dec(v_l_1284_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1884_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_size_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v_size_1875_ = lean_ctor_get(v_r_1868_, 0);
v___x_1876_ = lean_nat_add(v___x_1776_, v_size_1869_);
lean_dec(v_size_1869_);
v___x_1877_ = lean_nat_add(v___x_1776_, v_size_1875_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 4, v_impl_1775_);
lean_ctor_set(v___x_1873_, 3, v_r_1868_);
lean_ctor_set(v___x_1873_, 2, v_v_1283_);
lean_ctor_set(v___x_1873_, 1, v_k_1282_);
lean_ctor_set(v___x_1873_, 0, v___x_1877_);
v___x_1879_ = v___x_1873_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_r_1868_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v_impl_1775_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1879_);
lean_ctor_set(v___x_1287_, 3, v_l_1867_);
lean_ctor_set(v___x_1287_, 2, v_v_1871_);
lean_ctor_set(v___x_1287_, 1, v_k_1870_);
lean_ctor_set(v___x_1287_, 0, v___x_1876_);
v___x_1881_ = v___x_1287_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_k_1870_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_v_1871_);
lean_ctor_set(v_reuseFailAlloc_1882_, 3, v_l_1867_);
lean_ctor_set(v_reuseFailAlloc_1882_, 4, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_k_1887_; lean_object* v_v_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1899_; 
v_k_1887_ = lean_ctor_get(v_l_1284_, 1);
v_v_1888_ = lean_ctor_get(v_l_1284_, 2);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; lean_object* v_unused_1901_; lean_object* v_unused_1902_; 
v_unused_1900_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1901_);
v_unused_1902_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1902_);
v___x_1890_ = v_l_1284_;
v_isShared_1891_ = v_isSharedCheck_1899_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_v_1888_);
lean_inc(v_k_1887_);
lean_dec(v_l_1284_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1899_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_unsigned_to_nat(3u);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 3, v_r_1868_);
lean_ctor_set(v___x_1890_, 2, v_v_1283_);
lean_ctor_set(v___x_1890_, 1, v_k_1282_);
lean_ctor_set(v___x_1890_, 0, v___x_1776_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_r_1868_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_r_1868_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1894_);
lean_ctor_set(v___x_1287_, 3, v_l_1867_);
lean_ctor_set(v___x_1287_, 2, v_v_1888_);
lean_ctor_set(v___x_1287_, 1, v_k_1887_);
lean_ctor_set(v___x_1287_, 0, v___x_1892_);
v___x_1896_ = v___x_1287_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_1897_, 3, v_l_1867_);
lean_ctor_set(v_reuseFailAlloc_1897_, 4, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_object* v_r_1903_; 
v_r_1903_ = lean_ctor_get(v_l_1284_, 4);
lean_inc(v_r_1903_);
if (lean_obj_tag(v_r_1903_) == 0)
{
lean_object* v_k_1904_; lean_object* v_v_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1928_; 
lean_inc(v_l_1867_);
v_k_1904_ = lean_ctor_get(v_l_1284_, 1);
v_v_1905_ = lean_ctor_get(v_l_1284_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_l_1284_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1929_ = lean_ctor_get(v_l_1284_, 4);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_l_1284_, 3);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_l_1284_, 0);
lean_dec(v_unused_1931_);
v___x_1907_ = v_l_1284_;
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_v_1905_);
lean_inc(v_k_1904_);
lean_dec(v_l_1284_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1928_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_k_1909_; lean_object* v_v_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1924_; 
v_k_1909_ = lean_ctor_get(v_r_1903_, 1);
v_v_1910_ = lean_ctor_get(v_r_1903_, 2);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_r_1903_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1925_ = lean_ctor_get(v_r_1903_, 4);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_r_1903_, 3);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_r_1903_, 0);
lean_dec(v_unused_1927_);
v___x_1912_ = v_r_1903_;
v_isShared_1913_ = v_isSharedCheck_1924_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_v_1910_);
lean_inc(v_k_1909_);
lean_dec(v_r_1903_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1924_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(3u);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 4, v_l_1867_);
lean_ctor_set(v___x_1912_, 3, v_l_1867_);
lean_ctor_set(v___x_1912_, 2, v_v_1905_);
lean_ctor_set(v___x_1912_, 1, v_k_1904_);
lean_ctor_set(v___x_1912_, 0, v___x_1776_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1904_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1905_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_l_1867_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_l_1867_);
v___x_1916_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v_l_1867_);
lean_ctor_set(v___x_1907_, 2, v_v_1283_);
lean_ctor_set(v___x_1907_, 1, v_k_1282_);
lean_ctor_set(v___x_1907_, 0, v___x_1776_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1867_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_l_1867_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1918_);
lean_ctor_set(v___x_1287_, 3, v___x_1916_);
lean_ctor_set(v___x_1287_, 2, v_v_1910_);
lean_ctor_set(v___x_1287_, 1, v_k_1909_);
lean_ctor_set(v___x_1287_, 0, v___x_1914_);
v___x_1920_ = v___x_1287_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1909_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1910_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_unsigned_to_nat(2u);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_r_1903_);
lean_ctor_set(v___x_1287_, 0, v___x_1932_);
v___x_1934_ = v___x_1287_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_r_1903_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v___x_1937_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v_l_1284_);
lean_ctor_set(v___x_1287_, 0, v___x_1776_);
v___x_1937_ = v___x_1287_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1282_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1283_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_l_1284_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_l_1284_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
else
{
return v_t_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1941_, lean_object* v_t_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1941_, v_t_1942_);
lean_dec_ref(v_k_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1944_, lean_object* v_s_1945_){
_start:
{
lean_object* v_toRing_1946_; lean_object* v_invFn_x3f_1947_; lean_object* v_semiringId_x3f_1948_; lean_object* v_commSemiringInst_1949_; lean_object* v_commRingInst_1950_; lean_object* v_noZeroDivInst_x3f_1951_; lean_object* v_fieldInst_x3f_1952_; lean_object* v_powIdentityInst_x3f_1953_; lean_object* v_denoteEntries_1954_; lean_object* v_nextId_1955_; lean_object* v_steps_1956_; lean_object* v_queue_1957_; lean_object* v_basis_1958_; lean_object* v_diseqs_1959_; uint8_t v_recheck_1960_; lean_object* v_invSet_1961_; lean_object* v_powIdentityVarCount_1962_; lean_object* v_numEq0_x3f_1963_; uint8_t v_numEq0Updated_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_toRing_1946_ = lean_ctor_get(v_s_1945_, 0);
v_invFn_x3f_1947_ = lean_ctor_get(v_s_1945_, 1);
v_semiringId_x3f_1948_ = lean_ctor_get(v_s_1945_, 2);
v_commSemiringInst_1949_ = lean_ctor_get(v_s_1945_, 3);
v_commRingInst_1950_ = lean_ctor_get(v_s_1945_, 4);
v_noZeroDivInst_x3f_1951_ = lean_ctor_get(v_s_1945_, 5);
v_fieldInst_x3f_1952_ = lean_ctor_get(v_s_1945_, 6);
v_powIdentityInst_x3f_1953_ = lean_ctor_get(v_s_1945_, 7);
v_denoteEntries_1954_ = lean_ctor_get(v_s_1945_, 8);
v_nextId_1955_ = lean_ctor_get(v_s_1945_, 9);
v_steps_1956_ = lean_ctor_get(v_s_1945_, 10);
v_queue_1957_ = lean_ctor_get(v_s_1945_, 11);
v_basis_1958_ = lean_ctor_get(v_s_1945_, 12);
v_diseqs_1959_ = lean_ctor_get(v_s_1945_, 13);
v_recheck_1960_ = lean_ctor_get_uint8(v_s_1945_, sizeof(void*)*17);
v_invSet_1961_ = lean_ctor_get(v_s_1945_, 14);
v_powIdentityVarCount_1962_ = lean_ctor_get(v_s_1945_, 15);
v_numEq0_x3f_1963_ = lean_ctor_get(v_s_1945_, 16);
v_numEq0Updated_1964_ = lean_ctor_get_uint8(v_s_1945_, sizeof(void*)*17 + 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_s_1945_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v_s_1945_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_numEq0_x3f_1963_);
lean_inc(v_powIdentityVarCount_1962_);
lean_inc(v_invSet_1961_);
lean_inc(v_diseqs_1959_);
lean_inc(v_basis_1958_);
lean_inc(v_queue_1957_);
lean_inc(v_steps_1956_);
lean_inc(v_nextId_1955_);
lean_inc(v_denoteEntries_1954_);
lean_inc(v_powIdentityInst_x3f_1953_);
lean_inc(v_fieldInst_x3f_1952_);
lean_inc(v_noZeroDivInst_x3f_1951_);
lean_inc(v_commRingInst_1950_);
lean_inc(v_commSemiringInst_1949_);
lean_inc(v_semiringId_x3f_1948_);
lean_inc(v_invFn_x3f_1947_);
lean_inc(v_toRing_1946_);
lean_dec(v_s_1945_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1944_, v_queue_1957_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 11, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_toRing_1946_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_invFn_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_semiringId_x3f_1948_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_commSemiringInst_1949_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_commRingInst_1950_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_noZeroDivInst_x3f_1951_);
lean_ctor_set(v_reuseFailAlloc_1971_, 6, v_fieldInst_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 7, v_powIdentityInst_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_1971_, 8, v_denoteEntries_1954_);
lean_ctor_set(v_reuseFailAlloc_1971_, 9, v_nextId_1955_);
lean_ctor_set(v_reuseFailAlloc_1971_, 10, v_steps_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 11, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1971_, 12, v_basis_1958_);
lean_ctor_set(v_reuseFailAlloc_1971_, 13, v_diseqs_1959_);
lean_ctor_set(v_reuseFailAlloc_1971_, 14, v_invSet_1961_);
lean_ctor_set(v_reuseFailAlloc_1971_, 15, v_powIdentityVarCount_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 16, v_numEq0_x3f_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*17, v_recheck_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*17 + 1, v_numEq0Updated_1964_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1973_, lean_object* v_s_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1973_, v_s_1974_);
lean_dec_ref(v_val_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2028_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2028_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2028_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_queue_1993_; lean_object* v___x_1994_; 
v_queue_1993_ = lean_ctor_get(v_a_1989_, 11);
lean_inc(v_queue_1993_);
lean_dec(v_a_1989_);
v___x_1994_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1993_);
lean_dec(v_queue_1993_);
if (lean_obj_tag(v___x_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
lean_del_object(v___x_1991_);
v_val_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1995_);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1996_, 0, v_val_1995_);
v___x_1997_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1996_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec_ref_known(v___x_1997_, 1);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_1998_, v_a_1977_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1999_, 0);
lean_dec(v_unused_2007_);
v___x_2001_ = v___x_1999_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v___x_1999_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_1994_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1994_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref_known(v___x_1994_, 1);
v_a_2008_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1999_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1999_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref_known(v___x_1994_, 1);
v_a_2016_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1997_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1997_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v___x_1994_);
v___x_2024_ = lean_box(0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2024_);
v___x_2026_ = v___x_1991_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
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
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1988_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1988_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2050_, lean_object* v_k_2051_, lean_object* v_t_2052_, lean_object* v_h_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2051_, v_t_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2055_, lean_object* v_k_2056_, lean_object* v_t_2057_, lean_object* v_h_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2055_, v_k_2056_, v_t_2057_, v_h_2058_);
lean_dec_ref(v_k_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v_ks_2064_; lean_object* v_vs_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2089_; 
v_ks_2064_ = lean_ctor_get(v_x_2060_, 0);
v_vs_2065_ = lean_ctor_get(v_x_2060_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_x_2060_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2067_ = v_x_2060_;
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_vs_2065_);
lean_inc(v_ks_2064_);
lean_dec(v_x_2060_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2089_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_array_get_size(v_ks_2064_);
v___x_2070_ = lean_nat_dec_lt(v_x_2061_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_dec(v_x_2061_);
v___x_2071_ = lean_array_push(v_ks_2064_, v_x_2062_);
v___x_2072_ = lean_array_push(v_vs_2065_, v_x_2063_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2072_);
lean_ctor_set(v___x_2067_, 0, v___x_2071_);
v___x_2074_ = v___x_2067_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v_k_x27_2076_; uint8_t v___x_2077_; 
v_k_x27_2076_ = lean_array_fget_borrowed(v_ks_2064_, v_x_2061_);
v___x_2077_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2062_, v_k_x27_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2079_; 
if (v_isShared_2068_ == 0)
{
v___x_2079_ = v___x_2067_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_ks_2064_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_vs_2065_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_nat_add(v_x_2061_, v___x_2080_);
lean_dec(v_x_2061_);
v_x_2060_ = v___x_2079_;
v_x_2061_ = v___x_2081_;
goto _start;
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2084_ = lean_array_fset(v_ks_2064_, v_x_2061_, v_x_2062_);
v___x_2085_ = lean_array_fset(v_vs_2065_, v_x_2061_, v_x_2063_);
lean_dec(v_x_2061_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2085_);
lean_ctor_set(v___x_2067_, 0, v___x_2084_);
v___x_2087_ = v___x_2067_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2090_, lean_object* v_k_2091_, lean_object* v_v_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2090_, v___x_2093_, v_k_2091_, v_v_2092_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2096_, size_t v_x_2097_, size_t v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2096_) == 0)
{
lean_object* v_es_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v_j_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_es_2101_ = lean_ctor_get(v_x_2096_, 0);
v___x_2102_ = ((size_t)31ULL);
v___x_2103_ = lean_usize_land(v_x_2097_, v___x_2102_);
v_j_2104_ = lean_usize_to_nat(v___x_2103_);
v___x_2105_ = lean_array_get_size(v_es_2101_);
v___x_2106_ = lean_nat_dec_lt(v_j_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec(v_j_2104_);
lean_dec(v_x_2100_);
lean_dec_ref(v_x_2099_);
return v_x_2096_;
}
else
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2145_; 
lean_inc_ref(v_es_2101_);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_x_2096_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_x_2096_, 0);
lean_dec(v_unused_2146_);
v___x_2108_ = v_x_2096_;
v_isShared_2109_ = v_isSharedCheck_2145_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_x_2096_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2145_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_v_2110_; lean_object* v___x_2111_; lean_object* v_xs_x27_2112_; lean_object* v___y_2114_; 
v_v_2110_ = lean_array_fget(v_es_2101_, v_j_2104_);
v___x_2111_ = lean_box(0);
v_xs_x27_2112_ = lean_array_fset(v_es_2101_, v_j_2104_, v___x_2111_);
switch(lean_obj_tag(v_v_2110_))
{
case 0:
{
lean_object* v_key_2119_; lean_object* v_val_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2130_; 
v_key_2119_ = lean_ctor_get(v_v_2110_, 0);
v_val_2120_ = lean_ctor_get(v_v_2110_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_v_2110_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2122_ = v_v_2110_;
v_isShared_2123_ = v_isSharedCheck_2130_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_val_2120_);
lean_inc(v_key_2119_);
lean_dec(v_v_2110_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2130_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; 
v___x_2124_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2099_, v_key_2119_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_del_object(v___x_2122_);
v___x_2125_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2119_, v_val_2120_, v_x_2099_, v_x_2100_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___y_2114_ = v___x_2126_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_val_2120_);
lean_dec(v_key_2119_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_x_2100_);
lean_ctor_set(v___x_2122_, 0, v_x_2099_);
v___x_2128_ = v___x_2122_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_x_2099_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_x_2100_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
v___y_2114_ = v___x_2128_;
goto v___jp_2113_;
}
}
}
}
case 1:
{
lean_object* v_node_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2143_; 
v_node_2131_ = lean_ctor_get(v_v_2110_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_v_2110_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2133_ = v_v_2110_;
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_node_2131_);
lean_dec(v_v_2110_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2135_ = ((size_t)5ULL);
v___x_2136_ = lean_usize_shift_right(v_x_2097_, v___x_2135_);
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_add(v_x_2098_, v___x_2137_);
v___x_2139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2131_, v___x_2136_, v___x_2138_, v_x_2099_, v_x_2100_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2139_);
v___x_2141_ = v___x_2133_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v___y_2114_ = v___x_2141_;
goto v___jp_2113_;
}
}
}
default: 
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_x_2099_);
lean_ctor_set(v___x_2144_, 1, v_x_2100_);
v___y_2114_ = v___x_2144_;
goto v___jp_2113_;
}
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_array_fset(v_xs_x27_2112_, v_j_2104_, v___y_2114_);
lean_dec(v_j_2104_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2115_);
v___x_2117_ = v___x_2108_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
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
else
{
lean_object* v_ks_2147_; lean_object* v_vs_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2168_; 
v_ks_2147_ = lean_ctor_get(v_x_2096_, 0);
v_vs_2148_ = lean_ctor_get(v_x_2096_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2096_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2150_ = v_x_2096_;
v_isShared_2151_ = v_isSharedCheck_2168_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_vs_2148_);
lean_inc(v_ks_2147_);
lean_dec(v_x_2096_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2168_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_ks_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_vs_2148_);
v___x_2153_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v_newNode_2154_; uint8_t v___y_2156_; size_t v___x_2162_; uint8_t v___x_2163_; 
v_newNode_2154_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2153_, v_x_2099_, v_x_2100_);
v___x_2162_ = ((size_t)7ULL);
v___x_2163_ = lean_usize_dec_le(v___x_2162_, v_x_2098_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2164_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2154_);
v___x_2165_ = lean_unsigned_to_nat(4u);
v___x_2166_ = lean_nat_dec_lt(v___x_2164_, v___x_2165_);
lean_dec(v___x_2164_);
v___y_2156_ = v___x_2166_;
goto v___jp_2155_;
}
else
{
v___y_2156_ = v___x_2163_;
goto v___jp_2155_;
}
v___jp_2155_:
{
if (v___y_2156_ == 0)
{
lean_object* v_ks_2157_; lean_object* v_vs_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_ks_2157_ = lean_ctor_get(v_newNode_2154_, 0);
lean_inc_ref(v_ks_2157_);
v_vs_2158_ = lean_ctor_get(v_newNode_2154_, 1);
lean_inc_ref(v_vs_2158_);
lean_dec_ref(v_newNode_2154_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2098_, v_ks_2157_, v_vs_2158_, v___x_2159_, v___x_2160_);
lean_dec_ref(v_vs_2158_);
lean_dec_ref(v_ks_2157_);
return v___x_2161_;
}
else
{
return v_newNode_2154_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2169_, lean_object* v_keys_2170_, lean_object* v_vals_2171_, lean_object* v_i_2172_, lean_object* v_entries_2173_){
_start:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_array_get_size(v_keys_2170_);
v___x_2175_ = lean_nat_dec_lt(v_i_2172_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec(v_i_2172_);
return v_entries_2173_;
}
else
{
lean_object* v_k_2176_; lean_object* v_v_2177_; uint64_t v___x_2178_; size_t v_h_2179_; size_t v___x_2180_; lean_object* v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v_h_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_k_2176_ = lean_array_fget_borrowed(v_keys_2170_, v_i_2172_);
v_v_2177_ = lean_array_fget_borrowed(v_vals_2171_, v_i_2172_);
v___x_2178_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2176_);
v_h_2179_ = lean_uint64_to_usize(v___x_2178_);
v___x_2180_ = ((size_t)5ULL);
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = ((size_t)1ULL);
v___x_2183_ = lean_usize_sub(v_depth_2169_, v___x_2182_);
v___x_2184_ = lean_usize_mul(v___x_2180_, v___x_2183_);
v_h_2185_ = lean_usize_shift_right(v_h_2179_, v___x_2184_);
v___x_2186_ = lean_nat_add(v_i_2172_, v___x_2181_);
lean_dec(v_i_2172_);
lean_inc(v_v_2177_);
lean_inc(v_k_2176_);
v___x_2187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2173_, v_h_2185_, v_depth_2169_, v_k_2176_, v_v_2177_);
v_i_2172_ = v___x_2186_;
v_entries_2173_ = v___x_2187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2189_, lean_object* v_keys_2190_, lean_object* v_vals_2191_, lean_object* v_i_2192_, lean_object* v_entries_2193_){
_start:
{
size_t v_depth_boxed_2194_; lean_object* v_res_2195_; 
v_depth_boxed_2194_ = lean_unbox_usize(v_depth_2189_);
lean_dec(v_depth_2189_);
v_res_2195_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2194_, v_keys_2190_, v_vals_2191_, v_i_2192_, v_entries_2193_);
lean_dec_ref(v_vals_2191_);
lean_dec_ref(v_keys_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
size_t v_x_7232__boxed_2201_; size_t v_x_7233__boxed_2202_; lean_object* v_res_2203_; 
v_x_7232__boxed_2201_ = lean_unbox_usize(v_x_2197_);
lean_dec(v_x_2197_);
v_x_7233__boxed_2202_ = lean_unbox_usize(v_x_2198_);
lean_dec(v_x_2198_);
v_res_2203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2196_, v_x_7232__boxed_2201_, v_x_7233__boxed_2202_, v_x_2199_, v_x_2200_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
uint64_t v___x_2207_; size_t v___x_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2205_);
v___x_2208_ = lean_uint64_to_usize(v___x_2207_);
v___x_2209_ = ((size_t)1ULL);
v___x_2210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2204_, v___x_2208_, v___x_2209_, v_x_2205_, v_x_2206_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2211_, lean_object* v_ringId_2212_, lean_object* v_s_2213_){
_start:
{
lean_object* v_rings_2214_; lean_object* v_typeIdOf_2215_; lean_object* v_exprToRingId_2216_; lean_object* v_semirings_2217_; lean_object* v_stypeIdOf_2218_; lean_object* v_exprToSemiringId_2219_; lean_object* v_ncRings_2220_; lean_object* v_exprToNCRingId_2221_; lean_object* v_nctypeIdOf_2222_; lean_object* v_ncSemirings_2223_; lean_object* v_exprToNCSemiringId_2224_; lean_object* v_ncstypeIdOf_2225_; lean_object* v_steps_2226_; uint8_t v_reportedMaxDegreeIssue_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_rings_2214_ = lean_ctor_get(v_s_2213_, 0);
v_typeIdOf_2215_ = lean_ctor_get(v_s_2213_, 1);
v_exprToRingId_2216_ = lean_ctor_get(v_s_2213_, 2);
v_semirings_2217_ = lean_ctor_get(v_s_2213_, 3);
v_stypeIdOf_2218_ = lean_ctor_get(v_s_2213_, 4);
v_exprToSemiringId_2219_ = lean_ctor_get(v_s_2213_, 5);
v_ncRings_2220_ = lean_ctor_get(v_s_2213_, 6);
v_exprToNCRingId_2221_ = lean_ctor_get(v_s_2213_, 7);
v_nctypeIdOf_2222_ = lean_ctor_get(v_s_2213_, 8);
v_ncSemirings_2223_ = lean_ctor_get(v_s_2213_, 9);
v_exprToNCSemiringId_2224_ = lean_ctor_get(v_s_2213_, 10);
v_ncstypeIdOf_2225_ = lean_ctor_get(v_s_2213_, 11);
v_steps_2226_ = lean_ctor_get(v_s_2213_, 12);
v_reportedMaxDegreeIssue_2227_ = lean_ctor_get_uint8(v_s_2213_, sizeof(void*)*13);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_s_2213_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v_s_2213_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_steps_2226_);
lean_inc(v_ncstypeIdOf_2225_);
lean_inc(v_exprToNCSemiringId_2224_);
lean_inc(v_ncSemirings_2223_);
lean_inc(v_nctypeIdOf_2222_);
lean_inc(v_exprToNCRingId_2221_);
lean_inc(v_ncRings_2220_);
lean_inc(v_exprToSemiringId_2219_);
lean_inc(v_stypeIdOf_2218_);
lean_inc(v_semirings_2217_);
lean_inc(v_exprToRingId_2216_);
lean_inc(v_typeIdOf_2215_);
lean_inc(v_rings_2214_);
lean_dec(v_s_2213_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2216_, v_e_2211_, v_ringId_2212_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 2, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_rings_2214_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_typeIdOf_2215_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_semirings_2217_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_stypeIdOf_2218_);
lean_ctor_set(v_reuseFailAlloc_2234_, 5, v_exprToSemiringId_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 6, v_ncRings_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 7, v_exprToNCRingId_2221_);
lean_ctor_set(v_reuseFailAlloc_2234_, 8, v_nctypeIdOf_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 9, v_ncSemirings_2223_);
lean_ctor_set(v_reuseFailAlloc_2234_, 10, v_exprToNCSemiringId_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 11, v_ncstypeIdOf_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 12, v_steps_2226_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2227_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2239_, v_a_2241_, v_a_2246_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
if (lean_obj_tag(v_a_2253_) == 1)
{
lean_object* v_ringId_2254_; lean_object* v_val_2255_; uint8_t v___x_2256_; 
v_ringId_2254_ = lean_ctor_get(v_a_2240_, 0);
v_val_2255_ = lean_ctor_get(v_a_2253_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v_a_2253_, 1);
v___x_2256_ = lean_nat_dec_eq(v_val_2255_, v_ringId_2254_);
lean_dec(v_val_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2242_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v_verbose_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v_verbose_2259_ = lean_ctor_get_uint8(v_a_2258_, 0);
lean_dec(v_a_2258_);
if (v_verbose_2259_ == 0)
{
lean_dec_ref(v_e_2239_);
goto v___jp_2249_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2261_ = l_Lean_indentExpr(v_e_2239_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_Meta_Sym_reportIssue(v___x_2262_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_dec_ref_known(v___x_2263_, 1);
goto v___jp_2249_;
}
else
{
return v___x_2263_;
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v_e_2239_);
v_a_2264_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2257_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2257_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_dec_ref(v_e_2239_);
goto v___jp_2249_;
}
}
else
{
lean_object* v_ringId_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v_a_2253_);
v_ringId_2272_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_ringId_2272_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2273_, 0, v_e_2239_);
lean_closure_set(v___f_2273_, 1, v_ringId_2272_);
v___x_2274_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2275_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2274_, v___f_2273_, v_a_2241_);
return v___x_2275_;
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_e_2239_);
v_a_2276_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2252_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2252_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
v___jp_2249_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2295_, v_a_2296_, v_a_2297_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2324_, v_x_2325_, v_x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, size_t v_x_2330_, size_t v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2329_, v_x_2330_, v_x_2331_, v_x_2332_, v_x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v_x_7509__boxed_2341_; size_t v_x_7510__boxed_2342_; lean_object* v_res_2343_; 
v_x_7509__boxed_2341_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_x_7510__boxed_2342_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2335_, v_x_2336_, v_x_7509__boxed_2341_, v_x_7510__boxed_2342_, v_x_2339_, v_x_2340_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2344_, lean_object* v_n_2345_, lean_object* v_k_2346_, lean_object* v_v_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2345_, v_k_2346_, v_v_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2349_, size_t v_depth_2350_, lean_object* v_keys_2351_, lean_object* v_vals_2352_, lean_object* v_heq_2353_, lean_object* v_i_2354_, lean_object* v_entries_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2350_, v_keys_2351_, v_vals_2352_, v_i_2354_, v_entries_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2357_, lean_object* v_depth_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_entries_2363_){
_start:
{
size_t v_depth_boxed_2364_; lean_object* v_res_2365_; 
v_depth_boxed_2364_ = lean_unbox_usize(v_depth_2358_);
lean_dec(v_depth_2358_);
v_res_2365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2357_, v_depth_boxed_2364_, v_keys_2359_, v_vals_2360_, v_heq_2361_, v_i_2362_, v_entries_2363_);
lean_dec_ref(v_vals_2360_);
lean_dec_ref(v_keys_2359_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2367_, v_x_2368_, v_x_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2372_, lean_object* v___f_2373_, lean_object* v___f_2374_, lean_object* v_size_2375_, lean_object* v_s_2376_){
_start:
{
lean_object* v_id_2377_; lean_object* v_type_2378_; lean_object* v_u_2379_; lean_object* v_ringInst_2380_; lean_object* v_semiringInst_2381_; lean_object* v_charInst_x3f_2382_; lean_object* v_addFn_x3f_2383_; lean_object* v_mulFn_x3f_2384_; lean_object* v_subFn_x3f_2385_; lean_object* v_negFn_x3f_2386_; lean_object* v_powFn_x3f_2387_; lean_object* v_intCastFn_x3f_2388_; lean_object* v_natCastFn_x3f_2389_; lean_object* v_one_x3f_2390_; lean_object* v_vars_2391_; lean_object* v_varMap_2392_; lean_object* v_denote_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2402_; 
v_id_2377_ = lean_ctor_get(v_s_2376_, 0);
v_type_2378_ = lean_ctor_get(v_s_2376_, 1);
v_u_2379_ = lean_ctor_get(v_s_2376_, 2);
v_ringInst_2380_ = lean_ctor_get(v_s_2376_, 3);
v_semiringInst_2381_ = lean_ctor_get(v_s_2376_, 4);
v_charInst_x3f_2382_ = lean_ctor_get(v_s_2376_, 5);
v_addFn_x3f_2383_ = lean_ctor_get(v_s_2376_, 6);
v_mulFn_x3f_2384_ = lean_ctor_get(v_s_2376_, 7);
v_subFn_x3f_2385_ = lean_ctor_get(v_s_2376_, 8);
v_negFn_x3f_2386_ = lean_ctor_get(v_s_2376_, 9);
v_powFn_x3f_2387_ = lean_ctor_get(v_s_2376_, 10);
v_intCastFn_x3f_2388_ = lean_ctor_get(v_s_2376_, 11);
v_natCastFn_x3f_2389_ = lean_ctor_get(v_s_2376_, 12);
v_one_x3f_2390_ = lean_ctor_get(v_s_2376_, 13);
v_vars_2391_ = lean_ctor_get(v_s_2376_, 14);
v_varMap_2392_ = lean_ctor_get(v_s_2376_, 15);
v_denote_2393_ = lean_ctor_get(v_s_2376_, 16);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_s_2376_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2395_ = v_s_2376_;
v_isShared_2396_ = v_isSharedCheck_2402_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_denote_2393_);
lean_inc(v_varMap_2392_);
lean_inc(v_vars_2391_);
lean_inc(v_one_x3f_2390_);
lean_inc(v_natCastFn_x3f_2389_);
lean_inc(v_intCastFn_x3f_2388_);
lean_inc(v_powFn_x3f_2387_);
lean_inc(v_negFn_x3f_2386_);
lean_inc(v_subFn_x3f_2385_);
lean_inc(v_mulFn_x3f_2384_);
lean_inc(v_addFn_x3f_2383_);
lean_inc(v_charInst_x3f_2382_);
lean_inc(v_semiringInst_2381_);
lean_inc(v_ringInst_2380_);
lean_inc(v_u_2379_);
lean_inc(v_type_2378_);
lean_inc(v_id_2377_);
lean_dec(v_s_2376_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2402_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_inc_ref(v_e_2372_);
v___x_2397_ = l_Lean_PersistentArray_push___redArg(v_vars_2391_, v_e_2372_);
v___x_2398_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2373_, v___f_2374_, v_varMap_2392_, v_e_2372_, v_size_2375_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 15, v___x_2398_);
lean_ctor_set(v___x_2395_, 14, v___x_2397_);
v___x_2400_ = v___x_2395_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_id_2377_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_type_2378_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_u_2379_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_ringInst_2380_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_semiringInst_2381_);
lean_ctor_set(v_reuseFailAlloc_2401_, 5, v_charInst_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2401_, 6, v_addFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2401_, 7, v_mulFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2401_, 8, v_subFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2401_, 9, v_negFn_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2401_, 10, v_powFn_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2401_, 11, v_intCastFn_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2401_, 12, v_natCastFn_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2401_, 13, v_one_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2401_, 14, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2401_, 15, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 16, v_denote_2393_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2403_, lean_object* v_size_2404_, lean_object* v_____r_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_apply_2(v_toPure_2403_, lean_box(0), v_size_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2407_, lean_object* v_inst_2408_, lean_object* v_toBind_2409_, lean_object* v___f_2410_, lean_object* v_____r_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2412_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2413_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2413_, 0, lean_box(0));
lean_closure_set(v___x_2413_, 1, v___x_2412_);
lean_closure_set(v___x_2413_, 2, v_e_2407_);
v___x_2414_ = lean_apply_2(v_inst_2408_, lean_box(0), v___x_2413_);
v___x_2415_ = lean_apply_4(v_toBind_2409_, lean_box(0), lean_box(0), v___x_2414_, v___f_2410_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2416_, lean_object* v_e_2417_, lean_object* v_toBind_2418_, lean_object* v___f_2419_, lean_object* v_____r_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_apply_1(v_inst_2416_, v_e_2417_);
v___x_2422_ = lean_apply_4(v_toBind_2418_, lean_box(0), lean_box(0), v___x_2421_, v___f_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2423_, lean_object* v___f_2424_, lean_object* v_e_2425_, lean_object* v_toPure_2426_, lean_object* v_inst_2427_, lean_object* v_toBind_2428_, lean_object* v_inst_2429_, lean_object* v_modifyRing_2430_, lean_object* v_s_2431_){
_start:
{
lean_object* v_vars_2432_; lean_object* v_varMap_2433_; lean_object* v___x_2434_; 
v_vars_2432_ = lean_ctor_get(v_s_2431_, 14);
lean_inc_ref(v_vars_2432_);
v_varMap_2433_ = lean_ctor_get(v_s_2431_, 15);
lean_inc_ref(v_varMap_2433_);
lean_dec_ref(v_s_2431_);
lean_inc_ref(v_e_2425_);
lean_inc_ref(v___f_2424_);
lean_inc_ref(v___f_2423_);
v___x_2434_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2423_, v___f_2424_, v_varMap_2433_, v_e_2425_);
lean_dec_ref(v_varMap_2433_);
if (lean_obj_tag(v___x_2434_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v_vars_2432_);
lean_dec(v_modifyRing_2430_);
lean_dec(v_inst_2429_);
lean_dec(v_toBind_2428_);
lean_dec(v_inst_2427_);
lean_dec_ref(v_e_2425_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v___f_2423_);
v_val_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_val_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = lean_apply_2(v_toPure_2426_, lean_box(0), v_val_2435_);
return v___x_2436_;
}
else
{
lean_object* v_size_2437_; lean_object* v___f_2438_; lean_object* v___f_2439_; lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec(v___x_2434_);
v_size_2437_ = lean_ctor_get(v_vars_2432_, 2);
lean_inc_n(v_size_2437_, 2);
lean_dec_ref(v_vars_2432_);
lean_inc_ref_n(v_e_2425_, 2);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2438_, 0, v_e_2425_);
lean_closure_set(v___f_2438_, 1, v___f_2423_);
lean_closure_set(v___f_2438_, 2, v___f_2424_);
lean_closure_set(v___f_2438_, 3, v_size_2437_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2439_, 0, v_toPure_2426_);
lean_closure_set(v___f_2439_, 1, v_size_2437_);
lean_inc_n(v_toBind_2428_, 2);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2440_, 0, v_e_2425_);
lean_closure_set(v___f_2440_, 1, v_inst_2427_);
lean_closure_set(v___f_2440_, 2, v_toBind_2428_);
lean_closure_set(v___f_2440_, 3, v___f_2439_);
v___f_2441_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2441_, 0, v_inst_2429_);
lean_closure_set(v___f_2441_, 1, v_e_2425_);
lean_closure_set(v___f_2441_, 2, v_toBind_2428_);
lean_closure_set(v___f_2441_, 3, v___f_2440_);
v___x_2442_ = lean_apply_1(v_modifyRing_2430_, v___f_2438_);
v___x_2443_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v___x_2442_, v___f_2441_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_e_2450_){
_start:
{
lean_object* v_toApplicative_2451_; lean_object* v_toBind_2452_; lean_object* v_getRing_2453_; lean_object* v_modifyRing_2454_; lean_object* v_toPure_2455_; lean_object* v___f_2456_; lean_object* v___f_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; 
v_toApplicative_2451_ = lean_ctor_get(v_inst_2447_, 0);
lean_inc_ref(v_toApplicative_2451_);
v_toBind_2452_ = lean_ctor_get(v_inst_2447_, 1);
lean_inc_n(v_toBind_2452_, 2);
lean_dec_ref(v_inst_2447_);
v_getRing_2453_ = lean_ctor_get(v_inst_2448_, 0);
lean_inc(v_getRing_2453_);
v_modifyRing_2454_ = lean_ctor_get(v_inst_2448_, 1);
lean_inc(v_modifyRing_2454_);
lean_dec_ref(v_inst_2448_);
v_toPure_2455_ = lean_ctor_get(v_toApplicative_2451_, 1);
lean_inc(v_toPure_2455_);
lean_dec_ref(v_toApplicative_2451_);
v___f_2456_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2458_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2458_, 0, v___f_2456_);
lean_closure_set(v___f_2458_, 1, v___f_2457_);
lean_closure_set(v___f_2458_, 2, v_e_2450_);
lean_closure_set(v___f_2458_, 3, v_toPure_2455_);
lean_closure_set(v___f_2458_, 4, v_inst_2446_);
lean_closure_set(v___f_2458_, 5, v_toBind_2452_);
lean_closure_set(v___f_2458_, 6, v_inst_2449_);
lean_closure_set(v___f_2458_, 7, v_modifyRing_2454_);
v___x_2459_ = lean_apply_4(v_toBind_2452_, lean_box(0), lean_box(0), v_getRing_2453_, v___f_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_e_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2461_, v_inst_2462_, v_inst_2463_, v_inst_2464_, v_e_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2467_, v___y_2468_, v___y_2469_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2497_, lean_object* v_size_2498_, lean_object* v_s_2499_){
_start:
{
lean_object* v_toRing_2500_; lean_object* v_invFn_x3f_2501_; lean_object* v_semiringId_x3f_2502_; lean_object* v_commSemiringInst_2503_; lean_object* v_commRingInst_2504_; lean_object* v_noZeroDivInst_x3f_2505_; lean_object* v_fieldInst_x3f_2506_; lean_object* v_powIdentityInst_x3f_2507_; lean_object* v_denoteEntries_2508_; lean_object* v_nextId_2509_; lean_object* v_steps_2510_; lean_object* v_queue_2511_; lean_object* v_basis_2512_; lean_object* v_diseqs_2513_; uint8_t v_recheck_2514_; lean_object* v_invSet_2515_; lean_object* v_powIdentityVarCount_2516_; lean_object* v_numEq0_x3f_2517_; uint8_t v_numEq0Updated_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2551_; 
v_toRing_2500_ = lean_ctor_get(v_s_2499_, 0);
v_invFn_x3f_2501_ = lean_ctor_get(v_s_2499_, 1);
v_semiringId_x3f_2502_ = lean_ctor_get(v_s_2499_, 2);
v_commSemiringInst_2503_ = lean_ctor_get(v_s_2499_, 3);
v_commRingInst_2504_ = lean_ctor_get(v_s_2499_, 4);
v_noZeroDivInst_x3f_2505_ = lean_ctor_get(v_s_2499_, 5);
v_fieldInst_x3f_2506_ = lean_ctor_get(v_s_2499_, 6);
v_powIdentityInst_x3f_2507_ = lean_ctor_get(v_s_2499_, 7);
v_denoteEntries_2508_ = lean_ctor_get(v_s_2499_, 8);
v_nextId_2509_ = lean_ctor_get(v_s_2499_, 9);
v_steps_2510_ = lean_ctor_get(v_s_2499_, 10);
v_queue_2511_ = lean_ctor_get(v_s_2499_, 11);
v_basis_2512_ = lean_ctor_get(v_s_2499_, 12);
v_diseqs_2513_ = lean_ctor_get(v_s_2499_, 13);
v_recheck_2514_ = lean_ctor_get_uint8(v_s_2499_, sizeof(void*)*17);
v_invSet_2515_ = lean_ctor_get(v_s_2499_, 14);
v_powIdentityVarCount_2516_ = lean_ctor_get(v_s_2499_, 15);
v_numEq0_x3f_2517_ = lean_ctor_get(v_s_2499_, 16);
v_numEq0Updated_2518_ = lean_ctor_get_uint8(v_s_2499_, sizeof(void*)*17 + 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_s_2499_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2520_ = v_s_2499_;
v_isShared_2521_ = v_isSharedCheck_2551_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_numEq0_x3f_2517_);
lean_inc(v_powIdentityVarCount_2516_);
lean_inc(v_invSet_2515_);
lean_inc(v_diseqs_2513_);
lean_inc(v_basis_2512_);
lean_inc(v_queue_2511_);
lean_inc(v_steps_2510_);
lean_inc(v_nextId_2509_);
lean_inc(v_denoteEntries_2508_);
lean_inc(v_powIdentityInst_x3f_2507_);
lean_inc(v_fieldInst_x3f_2506_);
lean_inc(v_noZeroDivInst_x3f_2505_);
lean_inc(v_commRingInst_2504_);
lean_inc(v_commSemiringInst_2503_);
lean_inc(v_semiringId_x3f_2502_);
lean_inc(v_invFn_x3f_2501_);
lean_inc(v_toRing_2500_);
lean_dec(v_s_2499_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2551_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_id_2522_; lean_object* v_type_2523_; lean_object* v_u_2524_; lean_object* v_ringInst_2525_; lean_object* v_semiringInst_2526_; lean_object* v_charInst_x3f_2527_; lean_object* v_addFn_x3f_2528_; lean_object* v_mulFn_x3f_2529_; lean_object* v_subFn_x3f_2530_; lean_object* v_negFn_x3f_2531_; lean_object* v_powFn_x3f_2532_; lean_object* v_intCastFn_x3f_2533_; lean_object* v_natCastFn_x3f_2534_; lean_object* v_one_x3f_2535_; lean_object* v_vars_2536_; lean_object* v_varMap_2537_; lean_object* v_denote_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2550_; 
v_id_2522_ = lean_ctor_get(v_toRing_2500_, 0);
v_type_2523_ = lean_ctor_get(v_toRing_2500_, 1);
v_u_2524_ = lean_ctor_get(v_toRing_2500_, 2);
v_ringInst_2525_ = lean_ctor_get(v_toRing_2500_, 3);
v_semiringInst_2526_ = lean_ctor_get(v_toRing_2500_, 4);
v_charInst_x3f_2527_ = lean_ctor_get(v_toRing_2500_, 5);
v_addFn_x3f_2528_ = lean_ctor_get(v_toRing_2500_, 6);
v_mulFn_x3f_2529_ = lean_ctor_get(v_toRing_2500_, 7);
v_subFn_x3f_2530_ = lean_ctor_get(v_toRing_2500_, 8);
v_negFn_x3f_2531_ = lean_ctor_get(v_toRing_2500_, 9);
v_powFn_x3f_2532_ = lean_ctor_get(v_toRing_2500_, 10);
v_intCastFn_x3f_2533_ = lean_ctor_get(v_toRing_2500_, 11);
v_natCastFn_x3f_2534_ = lean_ctor_get(v_toRing_2500_, 12);
v_one_x3f_2535_ = lean_ctor_get(v_toRing_2500_, 13);
v_vars_2536_ = lean_ctor_get(v_toRing_2500_, 14);
v_varMap_2537_ = lean_ctor_get(v_toRing_2500_, 15);
v_denote_2538_ = lean_ctor_get(v_toRing_2500_, 16);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_toRing_2500_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2540_ = v_toRing_2500_;
v_isShared_2541_ = v_isSharedCheck_2550_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_denote_2538_);
lean_inc(v_varMap_2537_);
lean_inc(v_vars_2536_);
lean_inc(v_one_x3f_2535_);
lean_inc(v_natCastFn_x3f_2534_);
lean_inc(v_intCastFn_x3f_2533_);
lean_inc(v_powFn_x3f_2532_);
lean_inc(v_negFn_x3f_2531_);
lean_inc(v_subFn_x3f_2530_);
lean_inc(v_mulFn_x3f_2529_);
lean_inc(v_addFn_x3f_2528_);
lean_inc(v_charInst_x3f_2527_);
lean_inc(v_semiringInst_2526_);
lean_inc(v_ringInst_2525_);
lean_inc(v_u_2524_);
lean_inc(v_type_2523_);
lean_inc(v_id_2522_);
lean_dec(v_toRing_2500_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2550_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_inc_ref(v_e_2497_);
v___x_2542_ = l_Lean_PersistentArray_push___redArg(v_vars_2536_, v_e_2497_);
v___x_2543_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2537_, v_e_2497_, v_size_2498_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 15, v___x_2543_);
lean_ctor_set(v___x_2540_, 14, v___x_2542_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_id_2522_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_type_2523_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_u_2524_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_ringInst_2525_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_semiringInst_2526_);
lean_ctor_set(v_reuseFailAlloc_2549_, 5, v_charInst_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2549_, 6, v_addFn_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2549_, 7, v_mulFn_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2549_, 8, v_subFn_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2549_, 9, v_negFn_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2549_, 10, v_powFn_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2549_, 11, v_intCastFn_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2549_, 12, v_natCastFn_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2549_, 13, v_one_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2549_, 14, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2549_, 15, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2549_, 16, v_denote_2538_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2545_);
v___x_2547_ = v___x_2520_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_invFn_x3f_2501_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_semiringId_x3f_2502_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_commSemiringInst_2503_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_commRingInst_2504_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v_noZeroDivInst_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2548_, 6, v_fieldInst_x3f_2506_);
lean_ctor_set(v_reuseFailAlloc_2548_, 7, v_powIdentityInst_x3f_2507_);
lean_ctor_set(v_reuseFailAlloc_2548_, 8, v_denoteEntries_2508_);
lean_ctor_set(v_reuseFailAlloc_2548_, 9, v_nextId_2509_);
lean_ctor_set(v_reuseFailAlloc_2548_, 10, v_steps_2510_);
lean_ctor_set(v_reuseFailAlloc_2548_, 11, v_queue_2511_);
lean_ctor_set(v_reuseFailAlloc_2548_, 12, v_basis_2512_);
lean_ctor_set(v_reuseFailAlloc_2548_, 13, v_diseqs_2513_);
lean_ctor_set(v_reuseFailAlloc_2548_, 14, v_invSet_2515_);
lean_ctor_set(v_reuseFailAlloc_2548_, 15, v_powIdentityVarCount_2516_);
lean_ctor_set(v_reuseFailAlloc_2548_, 16, v_numEq0_x3f_2517_);
lean_ctor_set_uint8(v_reuseFailAlloc_2548_, sizeof(void*)*17, v_recheck_2514_);
lean_ctor_set_uint8(v_reuseFailAlloc_2548_, sizeof(void*)*17 + 1, v_numEq0Updated_2518_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2616_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2616_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2616_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_toRing_2570_; lean_object* v_vars_2571_; lean_object* v_varMap_2572_; lean_object* v___x_2573_; 
v_toRing_2570_ = lean_ctor_get(v_a_2566_, 0);
lean_inc_ref(v_toRing_2570_);
lean_dec(v_a_2566_);
v_vars_2571_ = lean_ctor_get(v_toRing_2570_, 14);
lean_inc_ref(v_vars_2571_);
v_varMap_2572_ = lean_ctor_get(v_toRing_2570_, 15);
lean_inc_ref(v_varMap_2572_);
lean_dec_ref(v_toRing_2570_);
v___x_2573_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2572_, v_e_2552_);
lean_dec_ref(v_varMap_2572_);
if (lean_obj_tag(v___x_2573_) == 1)
{
lean_object* v_val_2574_; lean_object* v___x_2576_; 
lean_dec_ref(v_vars_2571_);
lean_dec_ref(v_e_2552_);
v_val_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v_val_2574_);
v___x_2576_ = v___x_2568_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_val_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
else
{
lean_object* v_size_2578_; lean_object* v___f_2579_; lean_object* v___x_2580_; 
lean_dec(v___x_2573_);
lean_del_object(v___x_2568_);
v_size_2578_ = lean_ctor_get(v_vars_2571_, 2);
lean_inc_n(v_size_2578_, 2);
lean_dec_ref(v_vars_2571_);
lean_inc_ref(v_e_2552_);
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2579_, 0, v_e_2552_);
lean_closure_set(v___f_2579_, 1, v_size_2578_);
v___x_2580_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2579_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2580_, 1);
lean_inc_ref(v_e_2552_);
v___x_2581_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2552_, v___y_2553_, v___y_2554_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2581_, 1);
v___x_2582_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2583_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2582_, v_e_2552_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; 
v_unused_2591_ = lean_ctor_get(v___x_2583_, 0);
lean_dec(v_unused_2591_);
v___x_2585_ = v___x_2583_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v___x_2583_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_size_2578_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_size_2578_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_size_2578_);
v_a_2592_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2583_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_size_2578_);
lean_dec_ref(v_e_2552_);
v_a_2600_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2581_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2581_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_size_2578_);
lean_dec_ref(v_e_2552_);
v_a_2608_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2580_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2580_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_e_2552_);
v_a_2617_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2565_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2565_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2666_;
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
