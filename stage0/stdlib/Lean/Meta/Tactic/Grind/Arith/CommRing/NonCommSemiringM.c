// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
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
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`grind` internal error, invalid semiringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_semiringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg___boxed(lean_object* v_semiringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___redArg(v_semiringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(lean_object* v_00_u03b1_29_, lean_object* v_semiringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_semiringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_semiringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_run(v_00_u03b1_44_, v_semiringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Sym_canon(v_e_59_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_Sym_shareCommon(v_a_73_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_74_;
}
else
{
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__0(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v___y_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(lean_object* v_e_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_89_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1___boxed(lean_object* v_e_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommSemiringM___lam__1(v_e_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_toCold_132_; lean_object* v_mctx_133_; lean_object* v_lctx_134_; lean_object* v_options_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_toCold_132_ = lean_ctor_get(v___y_126_, 0);
v_mctx_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_133_);
lean_dec(v___x_131_);
v_lctx_134_ = lean_ctor_get(v___y_124_, 2);
v_options_135_ = lean_ctor_get(v_toCold_132_, 2);
lean_inc_ref(v_options_135_);
lean_inc_ref(v_lctx_134_);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v_env_130_);
lean_ctor_set(v___x_136_, 1, v_mctx_133_);
lean_ctor_set(v___x_136_, 2, v_lctx_134_);
lean_ctor_set(v___x_136_, 3, v_options_135_);
v___x_137_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_msgData_123_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 2);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc(v_ref_152_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_ref_152_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 0, v___x_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_174_, v_a_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_199_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_ncSemirings_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_ncSemirings_190_ = lean_ctor_get(v_a_186_, 9);
lean_inc_ref(v_ncSemirings_190_);
lean_dec(v_a_186_);
v___x_191_ = lean_array_get_size(v_ncSemirings_190_);
v___x_192_ = lean_nat_dec_lt(v_a_173_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref(v_ncSemirings_190_);
lean_del_object(v___x_188_);
v___x_193_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1);
v___x_194_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v___x_193_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_array_fget(v_ncSemirings_190_, v_a_173_);
lean_dec_ref(v_ncSemirings_190_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_195_);
v___x_197_ = v___x_188_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
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
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec(v_a_208_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object* v_00_u03b1_221_, lean_object* v_msg_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_222_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(v_00_u03b1_236_, v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object* v_a_251_, lean_object* v_f_252_, lean_object* v_s_253_){
_start:
{
lean_object* v_rings_254_; lean_object* v_typeIdOf_255_; lean_object* v_exprToRingId_256_; lean_object* v_semirings_257_; lean_object* v_stypeIdOf_258_; lean_object* v_exprToSemiringId_259_; lean_object* v_ncRings_260_; lean_object* v_exprToNCRingId_261_; lean_object* v_nctypeIdOf_262_; lean_object* v_ncSemirings_263_; lean_object* v_exprToNCSemiringId_264_; lean_object* v_ncstypeIdOf_265_; lean_object* v_steps_266_; uint8_t v_reportedMaxDegreeIssue_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_rings_254_ = lean_ctor_get(v_s_253_, 0);
v_typeIdOf_255_ = lean_ctor_get(v_s_253_, 1);
v_exprToRingId_256_ = lean_ctor_get(v_s_253_, 2);
v_semirings_257_ = lean_ctor_get(v_s_253_, 3);
v_stypeIdOf_258_ = lean_ctor_get(v_s_253_, 4);
v_exprToSemiringId_259_ = lean_ctor_get(v_s_253_, 5);
v_ncRings_260_ = lean_ctor_get(v_s_253_, 6);
v_exprToNCRingId_261_ = lean_ctor_get(v_s_253_, 7);
v_nctypeIdOf_262_ = lean_ctor_get(v_s_253_, 8);
v_ncSemirings_263_ = lean_ctor_get(v_s_253_, 9);
v_exprToNCSemiringId_264_ = lean_ctor_get(v_s_253_, 10);
v_ncstypeIdOf_265_ = lean_ctor_get(v_s_253_, 11);
v_steps_266_ = lean_ctor_get(v_s_253_, 12);
v_reportedMaxDegreeIssue_267_ = lean_ctor_get_uint8(v_s_253_, sizeof(void*)*13);
v___x_268_ = lean_array_get_size(v_ncSemirings_263_);
v___x_269_ = lean_nat_dec_lt(v_a_251_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec_ref(v_f_252_);
return v_s_253_;
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_281_; 
lean_inc(v_steps_266_);
lean_inc_ref(v_ncstypeIdOf_265_);
lean_inc_ref(v_exprToNCSemiringId_264_);
lean_inc_ref(v_ncSemirings_263_);
lean_inc_ref(v_nctypeIdOf_262_);
lean_inc_ref(v_exprToNCRingId_261_);
lean_inc_ref(v_ncRings_260_);
lean_inc_ref(v_exprToSemiringId_259_);
lean_inc_ref(v_stypeIdOf_258_);
lean_inc_ref(v_semirings_257_);
lean_inc_ref(v_exprToRingId_256_);
lean_inc_ref(v_typeIdOf_255_);
lean_inc_ref(v_rings_254_);
v_isSharedCheck_281_ = !lean_is_exclusive(v_s_253_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; 
v_unused_282_ = lean_ctor_get(v_s_253_, 12);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_253_, 11);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_253_, 10);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_253_, 9);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_253_, 8);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_253_, 7);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_253_, 6);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_253_, 5);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_253_, 4);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_253_, 3);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_253_, 2);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_s_253_, 1);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_s_253_, 0);
lean_dec(v_unused_294_);
v___x_271_ = v_s_253_;
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_s_253_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_281_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_v_273_; lean_object* v___x_274_; lean_object* v_xs_x27_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v_v_273_ = lean_array_fget(v_ncSemirings_263_, v_a_251_);
v___x_274_ = lean_box(0);
v_xs_x27_275_ = lean_array_fset(v_ncSemirings_263_, v_a_251_, v___x_274_);
v___x_276_ = lean_apply_1(v_f_252_, v_v_273_);
v___x_277_ = lean_array_fset(v_xs_x27_275_, v_a_251_, v___x_276_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 9, v___x_277_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_rings_254_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_typeIdOf_255_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_exprToRingId_256_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_semirings_257_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_stypeIdOf_258_);
lean_ctor_set(v_reuseFailAlloc_280_, 5, v_exprToSemiringId_259_);
lean_ctor_set(v_reuseFailAlloc_280_, 6, v_ncRings_260_);
lean_ctor_set(v_reuseFailAlloc_280_, 7, v_exprToNCRingId_261_);
lean_ctor_set(v_reuseFailAlloc_280_, 8, v_nctypeIdOf_262_);
lean_ctor_set(v_reuseFailAlloc_280_, 9, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 10, v_exprToNCSemiringId_264_);
lean_ctor_set(v_reuseFailAlloc_280_, 11, v_ncstypeIdOf_265_);
lean_ctor_set(v_reuseFailAlloc_280_, 12, v_steps_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*13, v_reportedMaxDegreeIssue_267_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object* v_a_295_, lean_object* v_f_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(v_a_295_, v_f_296_, v_s_297_);
lean_dec(v_a_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object* v_f_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_inc(v_a_300_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_303_, 0, v_a_300_);
lean_closure_set(v___f_303_, 1, v_f_299_);
v___x_304_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_305_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_304_, v___f_303_, v_a_301_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object* v_f_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec(v_a_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object* v_f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_311_, v_a_312_, v_a_313_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object* v_f_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
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
lean_dec(v_a_326_);
return v_res_338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0));
v___x_341_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed), 12, 0);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_344_, lean_object* v_vals_345_, lean_object* v_i_346_, lean_object* v_k_347_){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_keys_344_);
v___x_349_ = lean_nat_dec_lt(v_i_346_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec(v_i_346_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
else
{
lean_object* v_k_x27_351_; size_t v___x_352_; size_t v___x_353_; uint8_t v___x_354_; 
v_k_x27_351_ = lean_array_fget_borrowed(v_keys_344_, v_i_346_);
v___x_352_ = lean_ptr_addr(v_k_347_);
v___x_353_ = lean_ptr_addr(v_k_x27_351_);
v___x_354_ = lean_usize_dec_eq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_i_346_, v___x_355_);
lean_dec(v_i_346_);
v_i_346_ = v___x_356_;
goto _start;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_array_fget_borrowed(v_vals_345_, v_i_346_);
lean_dec(v_i_346_);
lean_inc(v___x_358_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_360_, lean_object* v_vals_361_, lean_object* v_i_362_, lean_object* v_k_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_360_, v_vals_361_, v_i_362_, v_k_363_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_vals_361_);
lean_dec_ref(v_keys_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_365_, size_t v_x_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_object* v_es_368_; lean_object* v___x_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v_j_372_; lean_object* v___x_373_; 
v_es_368_ = lean_ctor_get(v_x_365_, 0);
v___x_369_ = lean_box(2);
v___x_370_ = ((size_t)31ULL);
v___x_371_ = lean_usize_land(v_x_366_, v___x_370_);
v_j_372_ = lean_usize_to_nat(v___x_371_);
v___x_373_ = lean_array_get_borrowed(v___x_369_, v_es_368_, v_j_372_);
lean_dec(v_j_372_);
switch(lean_obj_tag(v___x_373_))
{
case 0:
{
lean_object* v_key_374_; lean_object* v_val_375_; size_t v___x_376_; size_t v___x_377_; uint8_t v___x_378_; 
v_key_374_ = lean_ctor_get(v___x_373_, 0);
v_val_375_ = lean_ctor_get(v___x_373_, 1);
v___x_376_ = lean_ptr_addr(v_x_367_);
v___x_377_ = lean_ptr_addr(v_key_374_);
v___x_378_ = lean_usize_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
lean_inc(v_val_375_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v_val_375_);
return v___x_380_;
}
}
case 1:
{
lean_object* v_node_381_; size_t v___x_382_; size_t v___x_383_; 
v_node_381_ = lean_ctor_get(v___x_373_, 0);
v___x_382_ = ((size_t)5ULL);
v___x_383_ = lean_usize_shift_right(v_x_366_, v___x_382_);
v_x_365_ = v_node_381_;
v_x_366_ = v___x_383_;
goto _start;
}
default: 
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
}
else
{
lean_object* v_ks_386_; lean_object* v_vs_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_ks_386_ = lean_ctor_get(v_x_365_, 0);
v_vs_387_ = lean_ctor_get(v_x_365_, 1);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_386_, v_vs_387_, v___x_388_, v_x_367_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
size_t v_x_904__boxed_393_; lean_object* v_res_394_; 
v_x_904__boxed_393_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_res_394_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_390_, v_x_904__boxed_393_, v_x_392_);
lean_dec_ref(v_x_392_);
lean_dec_ref(v_x_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; uint64_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_397_ = lean_ptr_addr(v_x_396_);
v___x_398_ = ((size_t)3ULL);
v___x_399_ = lean_usize_shift_right(v___x_397_, v___x_398_);
v___x_400_ = lean_usize_to_uint64(v___x_399_);
v___x_401_ = lean_uint64_to_usize(v___x_400_);
v___x_402_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_395_, v___x_401_, v_x_396_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_403_, v_x_404_);
lean_dec_ref(v_x_404_);
lean_dec_ref(v_x_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_420_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_420_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_exprToNCSemiringId_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v_exprToNCSemiringId_415_ = lean_ctor_get(v_a_411_, 10);
lean_inc_ref(v_exprToNCSemiringId_415_);
lean_dec(v_a_411_);
v___x_416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_exprToNCSemiringId_415_, v_e_406_);
lean_dec_ref(v_exprToNCSemiringId_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_416_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_410_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_410_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object* v_e_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_429_, v_a_430_, v_a_431_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_e_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object* v_e_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_434_, v_a_435_, v_a_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object* v_e_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
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
lean_dec_ref(v_e_447_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(v_00_u03b2_464_, v_x_465_, v_x_466_);
lean_dec_ref(v_x_466_);
lean_dec_ref(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, size_t v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_469_, v_x_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
size_t v_x_1025__boxed_477_; lean_object* v_res_478_; 
v_x_1025__boxed_477_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_478_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(v_00_u03b2_473_, v_x_474_, v_x_1025__boxed_477_, v_x_476_);
lean_dec_ref(v_x_476_);
lean_dec_ref(v_x_474_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_heq_482_, lean_object* v_i_483_, lean_object* v_k_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_480_, v_vals_481_, v_i_483_, v_k_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_486_, lean_object* v_keys_487_, lean_object* v_vals_488_, lean_object* v_heq_489_, lean_object* v_i_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_486_, v_keys_487_, v_vals_488_, v_heq_489_, v_i_490_, v_k_491_);
lean_dec_ref(v_k_491_);
lean_dec_ref(v_vals_488_);
lean_dec_ref(v_keys_487_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_ks_497_; lean_object* v_vs_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_524_; 
v_ks_497_ = lean_ctor_get(v_x_493_, 0);
v_vs_498_ = lean_ctor_get(v_x_493_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_524_ == 0)
{
v___x_500_ = v_x_493_;
v_isShared_501_ = v_isSharedCheck_524_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_vs_498_);
lean_inc(v_ks_497_);
lean_dec(v_x_493_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_524_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_array_get_size(v_ks_497_);
v___x_503_ = lean_nat_dec_lt(v_x_494_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec(v_x_494_);
v___x_504_ = lean_array_push(v_ks_497_, v_x_495_);
v___x_505_ = lean_array_push(v_vs_498_, v_x_496_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_505_);
lean_ctor_set(v___x_500_, 0, v___x_504_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
lean_object* v_k_x27_509_; size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v_k_x27_509_ = lean_array_fget_borrowed(v_ks_497_, v_x_494_);
v___x_510_ = lean_ptr_addr(v_x_495_);
v___x_511_ = lean_ptr_addr(v_k_x27_509_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
if (v_isShared_501_ == 0)
{
v___x_514_ = v___x_500_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_ks_497_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_vs_498_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_x_494_, v___x_515_);
lean_dec(v_x_494_);
v_x_493_ = v___x_514_;
v_x_494_ = v___x_516_;
goto _start;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_array_fset(v_ks_497_, v_x_494_, v_x_495_);
v___x_520_ = lean_array_fset(v_vs_498_, v_x_494_, v_x_496_);
lean_dec(v_x_494_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_520_);
lean_ctor_set(v___x_500_, 0, v___x_519_);
v___x_522_ = v___x_500_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_525_, lean_object* v_k_526_, lean_object* v_v_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_525_, v___x_528_, v_k_526_, v_v_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object* v_x_531_, size_t v_x_532_, size_t v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_es_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v_j_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_es_536_ = lean_ctor_get(v_x_531_, 0);
v___x_537_ = ((size_t)31ULL);
v___x_538_ = lean_usize_land(v_x_532_, v___x_537_);
v_j_539_ = lean_usize_to_nat(v___x_538_);
v___x_540_ = lean_array_get_size(v_es_536_);
v___x_541_ = lean_nat_dec_lt(v_j_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v_j_539_);
lean_dec(v_x_535_);
lean_dec_ref(v_x_534_);
return v_x_531_;
}
else
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_582_; 
lean_inc_ref(v_es_536_);
v_isSharedCheck_582_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v_x_531_, 0);
lean_dec(v_unused_583_);
v___x_543_ = v_x_531_;
v_isShared_544_ = v_isSharedCheck_582_;
goto v_resetjp_542_;
}
else
{
lean_dec(v_x_531_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_582_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_v_545_; lean_object* v___x_546_; lean_object* v_xs_x27_547_; lean_object* v___y_549_; 
v_v_545_ = lean_array_fget(v_es_536_, v_j_539_);
v___x_546_ = lean_box(0);
v_xs_x27_547_ = lean_array_fset(v_es_536_, v_j_539_, v___x_546_);
switch(lean_obj_tag(v_v_545_))
{
case 0:
{
lean_object* v_key_554_; lean_object* v_val_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_567_; 
v_key_554_ = lean_ctor_get(v_v_545_, 0);
v_val_555_ = lean_ctor_get(v_v_545_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_545_);
if (v_isSharedCheck_567_ == 0)
{
v___x_557_ = v_v_545_;
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_val_555_);
lean_inc(v_key_554_);
lean_dec(v_v_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_567_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_ptr_addr(v_x_534_);
v___x_560_ = lean_ptr_addr(v_key_554_);
v___x_561_ = lean_usize_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_del_object(v___x_557_);
v___x_562_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_554_, v_val_555_, v_x_534_, v_x_535_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
v___y_549_ = v___x_563_;
goto v___jp_548_;
}
else
{
lean_object* v___x_565_; 
lean_dec(v_val_555_);
lean_dec(v_key_554_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_x_535_);
lean_ctor_set(v___x_557_, 0, v_x_534_);
v___x_565_ = v___x_557_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_x_534_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_x_535_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v___y_549_ = v___x_565_;
goto v___jp_548_;
}
}
}
}
case 1:
{
lean_object* v_node_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
v_node_568_ = lean_ctor_get(v_v_545_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_v_545_);
if (v_isSharedCheck_580_ == 0)
{
v___x_570_ = v_v_545_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_node_568_);
lean_dec(v_v_545_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_usize_shift_right(v_x_532_, v___x_572_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_x_533_, v___x_574_);
v___x_576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_node_568_, v___x_573_, v___x_575_, v_x_534_, v_x_535_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_576_);
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v___y_549_ = v___x_578_;
goto v___jp_548_;
}
}
}
default: 
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_x_534_);
lean_ctor_set(v___x_581_, 1, v_x_535_);
v___y_549_ = v___x_581_;
goto v___jp_548_;
}
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_array_fset(v_xs_x27_547_, v_j_539_, v___y_549_);
lean_dec(v_j_539_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_550_);
v___x_552_ = v___x_543_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
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
else
{
lean_object* v_ks_584_; lean_object* v_vs_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_603_; 
v_ks_584_ = lean_ctor_get(v_x_531_, 0);
v_vs_585_ = lean_ctor_get(v_x_531_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_603_ == 0)
{
v___x_587_ = v_x_531_;
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_vs_585_);
lean_inc(v_ks_584_);
lean_dec(v_x_531_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_603_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_ks_584_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_vs_585_);
v___x_590_ = v_reuseFailAlloc_602_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v_newNode_591_; size_t v___x_592_; uint8_t v___x_593_; 
v_newNode_591_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v___x_590_, v_x_534_, v_x_535_);
v___x_592_ = ((size_t)7ULL);
v___x_593_ = lean_usize_dec_le(v___x_592_, v_x_533_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_591_);
v___x_595_ = lean_unsigned_to_nat(4u);
v___x_596_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v_ks_597_; lean_object* v_vs_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_ks_597_ = lean_ctor_get(v_newNode_591_, 0);
lean_inc_ref(v_ks_597_);
v_vs_598_ = lean_ctor_get(v_newNode_591_, 1);
lean_inc_ref(v_vs_598_);
lean_dec_ref(v_newNode_591_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_601_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_x_533_, v_ks_597_, v_vs_598_, v___x_599_, v___x_600_);
lean_dec_ref(v_vs_598_);
lean_dec_ref(v_ks_597_);
return v___x_601_;
}
else
{
return v_newNode_591_;
}
}
else
{
return v_newNode_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_i_607_, lean_object* v_entries_608_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_array_get_size(v_keys_605_);
v___x_610_ = lean_nat_dec_lt(v_i_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec(v_i_607_);
return v_entries_608_;
}
else
{
lean_object* v_k_611_; lean_object* v_v_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; uint64_t v___x_616_; size_t v_h_617_; size_t v___x_618_; lean_object* v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v_h_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_k_611_ = lean_array_fget_borrowed(v_keys_605_, v_i_607_);
v_v_612_ = lean_array_fget_borrowed(v_vals_606_, v_i_607_);
v___x_613_ = lean_ptr_addr(v_k_611_);
v___x_614_ = ((size_t)3ULL);
v___x_615_ = lean_usize_shift_right(v___x_613_, v___x_614_);
v___x_616_ = lean_usize_to_uint64(v___x_615_);
v_h_617_ = lean_uint64_to_usize(v___x_616_);
v___x_618_ = ((size_t)5ULL);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_sub(v_depth_604_, v___x_620_);
v___x_622_ = lean_usize_mul(v___x_618_, v___x_621_);
v_h_623_ = lean_usize_shift_right(v_h_617_, v___x_622_);
v___x_624_ = lean_nat_add(v_i_607_, v___x_619_);
lean_dec(v_i_607_);
lean_inc(v_v_612_);
lean_inc(v_k_611_);
v___x_625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_entries_608_, v_h_623_, v_depth_604_, v_k_611_, v_v_612_);
v_i_607_ = v___x_624_;
v_entries_608_ = v___x_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_627_, lean_object* v_keys_628_, lean_object* v_vals_629_, lean_object* v_i_630_, lean_object* v_entries_631_){
_start:
{
size_t v_depth_boxed_632_; lean_object* v_res_633_; 
v_depth_boxed_632_ = lean_unbox_usize(v_depth_627_);
lean_dec(v_depth_627_);
v_res_633_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_632_, v_keys_628_, v_vals_629_, v_i_630_, v_entries_631_);
lean_dec_ref(v_vals_629_);
lean_dec_ref(v_keys_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
size_t v_x_7704__boxed_639_; size_t v_x_7705__boxed_640_; lean_object* v_res_641_; 
v_x_7704__boxed_639_ = lean_unbox_usize(v_x_635_);
lean_dec(v_x_635_);
v_x_7705__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_634_, v_x_7704__boxed_639_, v_x_7705__boxed_640_, v_x_637_, v_x_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; uint64_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_645_ = lean_ptr_addr(v_x_643_);
v___x_646_ = ((size_t)3ULL);
v___x_647_ = lean_usize_shift_right(v___x_645_, v___x_646_);
v___x_648_ = lean_usize_to_uint64(v___x_647_);
v___x_649_ = lean_uint64_to_usize(v___x_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_642_, v___x_649_, v___x_650_, v_x_643_, v_x_644_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_s_654_){
_start:
{
lean_object* v_rings_655_; lean_object* v_typeIdOf_656_; lean_object* v_exprToRingId_657_; lean_object* v_semirings_658_; lean_object* v_stypeIdOf_659_; lean_object* v_exprToSemiringId_660_; lean_object* v_ncRings_661_; lean_object* v_exprToNCRingId_662_; lean_object* v_nctypeIdOf_663_; lean_object* v_ncSemirings_664_; lean_object* v_exprToNCSemiringId_665_; lean_object* v_ncstypeIdOf_666_; lean_object* v_steps_667_; uint8_t v_reportedMaxDegreeIssue_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_rings_655_ = lean_ctor_get(v_s_654_, 0);
v_typeIdOf_656_ = lean_ctor_get(v_s_654_, 1);
v_exprToRingId_657_ = lean_ctor_get(v_s_654_, 2);
v_semirings_658_ = lean_ctor_get(v_s_654_, 3);
v_stypeIdOf_659_ = lean_ctor_get(v_s_654_, 4);
v_exprToSemiringId_660_ = lean_ctor_get(v_s_654_, 5);
v_ncRings_661_ = lean_ctor_get(v_s_654_, 6);
v_exprToNCRingId_662_ = lean_ctor_get(v_s_654_, 7);
v_nctypeIdOf_663_ = lean_ctor_get(v_s_654_, 8);
v_ncSemirings_664_ = lean_ctor_get(v_s_654_, 9);
v_exprToNCSemiringId_665_ = lean_ctor_get(v_s_654_, 10);
v_ncstypeIdOf_666_ = lean_ctor_get(v_s_654_, 11);
v_steps_667_ = lean_ctor_get(v_s_654_, 12);
v_reportedMaxDegreeIssue_668_ = lean_ctor_get_uint8(v_s_654_, sizeof(void*)*13);
v_isSharedCheck_676_ = !lean_is_exclusive(v_s_654_);
if (v_isSharedCheck_676_ == 0)
{
v___x_670_ = v_s_654_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_steps_667_);
lean_inc(v_ncstypeIdOf_666_);
lean_inc(v_exprToNCSemiringId_665_);
lean_inc(v_ncSemirings_664_);
lean_inc(v_nctypeIdOf_663_);
lean_inc(v_exprToNCRingId_662_);
lean_inc(v_ncRings_661_);
lean_inc(v_exprToSemiringId_660_);
lean_inc(v_stypeIdOf_659_);
lean_inc(v_semirings_658_);
lean_inc(v_exprToRingId_657_);
lean_inc(v_typeIdOf_656_);
lean_inc(v_rings_655_);
lean_dec(v_s_654_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
lean_inc(v_a_653_);
v___x_672_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_exprToNCSemiringId_665_, v_e_652_, v_a_653_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 10, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_rings_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_typeIdOf_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_exprToRingId_657_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_semirings_658_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_stypeIdOf_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v_exprToSemiringId_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_ncRings_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v_exprToNCRingId_662_);
lean_ctor_set(v_reuseFailAlloc_675_, 8, v_nctypeIdOf_663_);
lean_ctor_set(v_reuseFailAlloc_675_, 9, v_ncSemirings_664_);
lean_ctor_set(v_reuseFailAlloc_675_, 10, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 11, v_ncstypeIdOf_666_);
lean_ctor_set(v_reuseFailAlloc_675_, 12, v_steps_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*13, v_reportedMaxDegreeIssue_668_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(v_e_677_, v_a_678_, v_s_679_);
lean_dec(v_a_678_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_684_, v_a_686_, v_a_691_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
if (lean_obj_tag(v_a_698_) == 1)
{
lean_object* v_val_699_; uint8_t v___x_700_; 
v_val_699_ = lean_ctor_get(v_a_698_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_a_698_, 1);
v___x_700_ = lean_nat_dec_eq(v_val_699_, v_a_685_);
lean_dec(v_val_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_687_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v_verbose_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v_verbose_703_ = lean_ctor_get_uint8(v_a_702_, 0);
lean_dec(v_a_702_);
if (v_verbose_703_ == 0)
{
lean_dec_ref(v_e_684_);
goto v___jp_694_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1);
v___x_705_ = l_Lean_indentExpr(v_e_684_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = l_Lean_Meta_Sym_reportIssue(v___x_706_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_dec_ref_known(v___x_707_, 1);
goto v___jp_694_;
}
else
{
return v___x_707_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_e_684_);
v_a_708_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_701_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_701_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_dec_ref(v_e_684_);
goto v___jp_694_;
}
}
else
{
lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_a_698_);
lean_inc(v_a_685_);
v___f_716_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_716_, 0, v_e_684_);
lean_closure_set(v___f_716_, 1, v_a_685_);
v___x_717_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_717_, v___f_716_, v_a_686_);
return v___x_718_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v_e_684_);
v_a_719_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_697_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_697_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
v___jp_694_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object* v_e_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec(v_a_728_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object* v_e_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_738_, v_a_739_, v_a_740_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object* v_e_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
lean_dec(v_a_753_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_x_767_, v_x_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, size_t v_x_773_, size_t v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_772_, v_x_773_, v_x_774_, v_x_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
size_t v_x_7990__boxed_784_; size_t v_x_7991__boxed_785_; lean_object* v_res_786_; 
v_x_7990__boxed_784_ = lean_unbox_usize(v_x_780_);
lean_dec(v_x_780_);
v_x_7991__boxed_785_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(v_00_u03b2_778_, v_x_779_, v_x_7990__boxed_784_, v_x_7991__boxed_785_, v_x_782_, v_x_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_787_, lean_object* v_n_788_, lean_object* v_k_789_, lean_object* v_v_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v_n_788_, v_k_789_, v_v_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_792_, size_t v_depth_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_heq_796_, lean_object* v_i_797_, lean_object* v_entries_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_793_, v_keys_794_, v_vals_795_, v_i_797_, v_entries_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_800_, lean_object* v_depth_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_entries_806_){
_start:
{
size_t v_depth_boxed_807_; lean_object* v_res_808_; 
v_depth_boxed_807_ = lean_unbox_usize(v_depth_801_);
lean_dec(v_depth_801_);
v_res_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_800_, v_depth_boxed_807_, v_keys_802_, v_vals_803_, v_heq_804_, v_i_805_, v_entries_806_);
lean_dec_ref(v_vals_803_);
lean_dec_ref(v_keys_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_810_, v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object* v_e_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_815_, v___y_816_, v___y_817_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object* v_e_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
return v_res_842_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
}
#ifdef __cplusplus
}
#endif
