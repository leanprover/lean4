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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v___x_72_);
v___x_74_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_73_, v___y_66_);
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
v___x_102_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_89_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
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
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_mctx_132_; lean_object* v_lctx_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_mctx_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_132_);
lean_dec(v___x_131_);
v_lctx_133_ = lean_ctor_get(v___y_124_, 2);
v_options_134_ = lean_ctor_get(v___y_126_, 2);
lean_inc_ref(v_options_134_);
lean_inc_ref(v_lctx_133_);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v_env_130_);
lean_ctor_set(v___x_135_, 1, v_mctx_132_);
lean_ctor_set(v___x_135_, 2, v_lctx_133_);
lean_ctor_set(v___x_135_, 3, v_options_134_);
v___x_136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_msgData_123_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msgData_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_ref_151_ = lean_ctor_get(v___y_148_, 5);
v___x_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0_spec__0(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_inc(v_ref_151_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_ref_151_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg___boxed(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__0));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_173_, v_a_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_198_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_198_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_ncSemirings_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_ncSemirings_189_ = lean_ctor_get(v_a_185_, 9);
lean_inc_ref(v_ncSemirings_189_);
lean_dec(v_a_185_);
v___x_190_ = lean_array_get_size(v_ncSemirings_189_);
v___x_191_ = lean_nat_dec_lt(v_a_172_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec_ref(v_ncSemirings_189_);
lean_del_object(v___x_187_);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___closed__1);
v___x_193_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v___x_192_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_array_fget(v_ncSemirings_189_, v_a_172_);
lean_dec_ref(v_ncSemirings_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_194_);
v___x_196_ = v___x_187_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_184_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_184_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed(lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(lean_object* v_00_u03b1_220_, lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___redArg(v_msg_221_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring_spec__0(v_00_u03b1_235_, v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec(v___y_237_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(lean_object* v_a_250_, lean_object* v_f_251_, lean_object* v_s_252_){
_start:
{
lean_object* v_rings_253_; lean_object* v_typeIdOf_254_; lean_object* v_exprToRingId_255_; lean_object* v_semirings_256_; lean_object* v_stypeIdOf_257_; lean_object* v_exprToSemiringId_258_; lean_object* v_ncRings_259_; lean_object* v_exprToNCRingId_260_; lean_object* v_nctypeIdOf_261_; lean_object* v_ncSemirings_262_; lean_object* v_exprToNCSemiringId_263_; lean_object* v_ncstypeIdOf_264_; lean_object* v_steps_265_; uint8_t v_reportedMaxDegreeIssue_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_rings_253_ = lean_ctor_get(v_s_252_, 0);
v_typeIdOf_254_ = lean_ctor_get(v_s_252_, 1);
v_exprToRingId_255_ = lean_ctor_get(v_s_252_, 2);
v_semirings_256_ = lean_ctor_get(v_s_252_, 3);
v_stypeIdOf_257_ = lean_ctor_get(v_s_252_, 4);
v_exprToSemiringId_258_ = lean_ctor_get(v_s_252_, 5);
v_ncRings_259_ = lean_ctor_get(v_s_252_, 6);
v_exprToNCRingId_260_ = lean_ctor_get(v_s_252_, 7);
v_nctypeIdOf_261_ = lean_ctor_get(v_s_252_, 8);
v_ncSemirings_262_ = lean_ctor_get(v_s_252_, 9);
v_exprToNCSemiringId_263_ = lean_ctor_get(v_s_252_, 10);
v_ncstypeIdOf_264_ = lean_ctor_get(v_s_252_, 11);
v_steps_265_ = lean_ctor_get(v_s_252_, 12);
v_reportedMaxDegreeIssue_266_ = lean_ctor_get_uint8(v_s_252_, sizeof(void*)*13);
v___x_267_ = lean_array_get_size(v_ncSemirings_262_);
v___x_268_ = lean_nat_dec_lt(v_a_250_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_f_251_);
return v_s_252_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
lean_inc(v_steps_265_);
lean_inc_ref(v_ncstypeIdOf_264_);
lean_inc_ref(v_exprToNCSemiringId_263_);
lean_inc_ref(v_ncSemirings_262_);
lean_inc_ref(v_nctypeIdOf_261_);
lean_inc_ref(v_exprToNCRingId_260_);
lean_inc_ref(v_ncRings_259_);
lean_inc_ref(v_exprToSemiringId_258_);
lean_inc_ref(v_stypeIdOf_257_);
lean_inc_ref(v_semirings_256_);
lean_inc_ref(v_exprToRingId_255_);
lean_inc_ref(v_typeIdOf_254_);
lean_inc_ref(v_rings_253_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_252_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_281_ = lean_ctor_get(v_s_252_, 12);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_252_, 11);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_252_, 10);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_252_, 9);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_252_, 8);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_252_, 7);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_252_, 6);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_252_, 5);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_252_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_252_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_252_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_252_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_s_252_, 0);
lean_dec(v_unused_293_);
v___x_270_ = v_s_252_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_s_252_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_v_272_ = lean_array_fget(v_ncSemirings_262_, v_a_250_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_ncSemirings_262_, v_a_250_, v___x_273_);
v___x_275_ = lean_apply_1(v_f_251_, v_v_272_);
v___x_276_ = lean_array_fset(v_xs_x27_274_, v_a_250_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 9, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_rings_253_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_typeIdOf_254_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_exprToRingId_255_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_semirings_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_stypeIdOf_257_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_exprToSemiringId_258_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_ncRings_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_exprToNCRingId_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_nctypeIdOf_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 10, v_exprToNCSemiringId_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 11, v_ncstypeIdOf_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 12, v_steps_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*13, v_reportedMaxDegreeIssue_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed(lean_object* v_a_294_, lean_object* v_f_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0(v_a_294_, v_f_295_, v_s_296_);
lean_dec(v_a_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_a_299_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v_a_299_);
lean_closure_set(v___f_302_, 1, v_f_298_);
v___x_303_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_304_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_303_, v___f_302_, v_a_300_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg___boxed(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(lean_object* v_f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v_f_310_, v_a_311_, v_a_312_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___boxed(lean_object* v_f_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring(v_f_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__0));
v___x_340_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring___boxed), 12, 0);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringNonCommSemiringM___closed__1);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_343_, lean_object* v_vals_344_, lean_object* v_i_345_, lean_object* v_k_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_array_get_size(v_keys_343_);
v___x_348_ = lean_nat_dec_lt(v_i_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_i_345_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
else
{
lean_object* v_k_x27_350_; uint8_t v___x_351_; 
v_k_x27_350_ = lean_array_fget_borrowed(v_keys_343_, v_i_345_);
v___x_351_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_346_, v_k_x27_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_i_345_, v___x_352_);
lean_dec(v_i_345_);
v_i_345_ = v___x_353_;
goto _start;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_array_fget_borrowed(v_vals_344_, v_i_345_);
lean_dec(v_i_345_);
lean_inc(v___x_355_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_357_, lean_object* v_vals_358_, lean_object* v_i_359_, lean_object* v_k_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_357_, v_vals_358_, v_i_359_, v_k_360_);
lean_dec_ref(v_k_360_);
lean_dec_ref(v_vals_358_);
lean_dec_ref(v_keys_357_);
return v_res_361_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; 
v___x_362_ = ((size_t)5ULL);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_shift_left(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; 
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_367_ = lean_usize_sub(v___x_366_, v___x_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_368_, size_t v_x_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_es_371_; lean_object* v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; lean_object* v_j_376_; lean_object* v___x_377_; 
v_es_371_ = lean_ctor_get(v_x_368_, 0);
v___x_372_ = lean_box(2);
v___x_373_ = ((size_t)5ULL);
v___x_374_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_375_ = lean_usize_land(v_x_369_, v___x_374_);
v_j_376_ = lean_usize_to_nat(v___x_375_);
v___x_377_ = lean_array_get_borrowed(v___x_372_, v_es_371_, v_j_376_);
lean_dec(v_j_376_);
switch(lean_obj_tag(v___x_377_))
{
case 0:
{
lean_object* v_key_378_; lean_object* v_val_379_; uint8_t v___x_380_; 
v_key_378_ = lean_ctor_get(v___x_377_, 0);
v_val_379_ = lean_ctor_get(v___x_377_, 1);
v___x_380_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_370_, v_key_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
lean_inc(v_val_379_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_val_379_);
return v___x_382_;
}
}
case 1:
{
lean_object* v_node_383_; size_t v___x_384_; 
v_node_383_ = lean_ctor_get(v___x_377_, 0);
v___x_384_ = lean_usize_shift_right(v_x_369_, v___x_373_);
v_x_368_ = v_node_383_;
v_x_369_ = v___x_384_;
goto _start;
}
default: 
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
}
else
{
lean_object* v_ks_387_; lean_object* v_vs_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_ks_387_ = lean_ctor_get(v_x_368_, 0);
v_vs_388_ = lean_ctor_get(v_x_368_, 1);
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_387_, v_vs_388_, v___x_389_, v_x_370_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
size_t v_x_867__boxed_394_; lean_object* v_res_395_; 
v_x_867__boxed_394_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_395_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_391_, v_x_867__boxed_394_, v_x_393_);
lean_dec_ref(v_x_393_);
lean_dec_ref(v_x_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
uint64_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_398_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_397_);
v___x_399_ = lean_uint64_to_usize(v___x_398_);
v___x_400_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_396_, v___x_399_, v_x_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_401_, v_x_402_);
lean_dec_ref(v_x_402_);
lean_dec_ref(v_x_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_418_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_exprToNCSemiringId_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_exprToNCSemiringId_413_ = lean_ctor_get(v_a_409_, 10);
lean_inc_ref(v_exprToNCSemiringId_413_);
lean_dec(v_a_409_);
v___x_414_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_exprToNCSemiringId_413_, v_e_404_);
lean_dec_ref(v_exprToNCSemiringId_413_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v_a_419_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_408_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_408_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg___boxed(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_427_, v_a_428_, v_a_429_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_e_427_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_432_, v_a_433_, v_a_441_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___boxed(lean_object* v_e_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f(v_e_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_e_445_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___redArg(v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0(v_00_u03b2_462_, v_x_463_, v_x_464_);
lean_dec_ref(v_x_464_);
lean_dec_ref(v_x_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, size_t v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg(v_x_467_, v_x_468_, v_x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
size_t v_x_984__boxed_475_; lean_object* v_res_476_; 
v_x_984__boxed_475_ = lean_unbox_usize(v_x_473_);
lean_dec(v_x_473_);
v_res_476_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0(v_00_u03b2_471_, v_x_472_, v_x_984__boxed_475_, v_x_474_);
lean_dec_ref(v_x_474_);
lean_dec_ref(v_x_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_477_, lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_heq_480_, lean_object* v_i_481_, lean_object* v_k_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_478_, v_vals_479_, v_i_481_, v_k_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_484_, lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_heq_487_, lean_object* v_i_488_, lean_object* v_k_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_484_, v_keys_485_, v_vals_486_, v_heq_487_, v_i_488_, v_k_489_);
lean_dec_ref(v_k_489_);
lean_dec_ref(v_vals_486_);
lean_dec_ref(v_keys_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v_ks_495_; lean_object* v_vs_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_520_; 
v_ks_495_ = lean_ctor_get(v_x_491_, 0);
v_vs_496_ = lean_ctor_get(v_x_491_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_491_);
if (v_isSharedCheck_520_ == 0)
{
v___x_498_ = v_x_491_;
v_isShared_499_ = v_isSharedCheck_520_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_vs_496_);
lean_inc(v_ks_495_);
lean_dec(v_x_491_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_520_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_array_get_size(v_ks_495_);
v___x_501_ = lean_nat_dec_lt(v_x_492_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_x_492_);
v___x_502_ = lean_array_push(v_ks_495_, v_x_493_);
v___x_503_ = lean_array_push(v_vs_496_, v_x_494_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_503_);
lean_ctor_set(v___x_498_, 0, v___x_502_);
v___x_505_ = v___x_498_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_k_x27_507_; uint8_t v___x_508_; 
v_k_x27_507_ = lean_array_fget_borrowed(v_ks_495_, v_x_492_);
v___x_508_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_493_, v_k_x27_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; 
if (v_isShared_499_ == 0)
{
v___x_510_ = v___x_498_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_ks_495_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_vs_496_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_add(v_x_492_, v___x_511_);
lean_dec(v_x_492_);
v_x_491_ = v___x_510_;
v_x_492_ = v___x_512_;
goto _start;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = lean_array_fset(v_ks_495_, v_x_492_, v_x_493_);
v___x_516_ = lean_array_fset(v_vs_496_, v_x_492_, v_x_494_);
lean_dec(v_x_492_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_516_);
lean_ctor_set(v___x_498_, 0, v___x_515_);
v___x_518_ = v___x_498_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_521_, lean_object* v_k_522_, lean_object* v_v_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_521_, v___x_524_, v_k_522_, v_v_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(lean_object* v_x_527_, size_t v_x_528_, size_t v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_es_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v_j_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_es_532_ = lean_ctor_get(v_x_527_, 0);
v___x_533_ = ((size_t)5ULL);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_536_ = lean_usize_land(v_x_528_, v___x_535_);
v_j_537_ = lean_usize_to_nat(v___x_536_);
v___x_538_ = lean_array_get_size(v_es_532_);
v___x_539_ = lean_nat_dec_lt(v_j_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v_j_537_);
lean_dec(v_x_531_);
lean_dec_ref(v_x_530_);
return v_x_527_;
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_576_; 
lean_inc_ref(v_es_532_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_527_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_x_527_, 0);
lean_dec(v_unused_577_);
v___x_541_ = v_x_527_;
v_isShared_542_ = v_isSharedCheck_576_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_x_527_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_576_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_v_543_; lean_object* v___x_544_; lean_object* v_xs_x27_545_; lean_object* v___y_547_; 
v_v_543_ = lean_array_fget(v_es_532_, v_j_537_);
v___x_544_ = lean_box(0);
v_xs_x27_545_ = lean_array_fset(v_es_532_, v_j_537_, v___x_544_);
switch(lean_obj_tag(v_v_543_))
{
case 0:
{
lean_object* v_key_552_; lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_563_; 
v_key_552_ = lean_ctor_get(v_v_543_, 0);
v_val_553_ = lean_ctor_get(v_v_543_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_555_ = v_v_543_;
v_isShared_556_ = v_isSharedCheck_563_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_inc(v_key_552_);
lean_dec(v_v_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_563_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v___x_557_; 
v___x_557_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_530_, v_key_552_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_del_object(v___x_555_);
v___x_558_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_552_, v_val_553_, v_x_530_, v_x_531_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___y_547_ = v___x_559_;
goto v___jp_546_;
}
else
{
lean_object* v___x_561_; 
lean_dec(v_val_553_);
lean_dec(v_key_552_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_x_531_);
lean_ctor_set(v___x_555_, 0, v_x_530_);
v___x_561_ = v___x_555_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_x_530_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_x_531_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_547_ = v___x_561_;
goto v___jp_546_;
}
}
}
}
case 1:
{
lean_object* v_node_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
v_node_564_ = lean_ctor_get(v_v_543_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_543_);
if (v_isSharedCheck_574_ == 0)
{
v___x_566_ = v_v_543_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_node_564_);
lean_dec(v_v_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_568_ = lean_usize_shift_right(v_x_528_, v___x_533_);
v___x_569_ = lean_usize_add(v_x_529_, v___x_534_);
v___x_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_node_564_, v___x_568_, v___x_569_, v_x_530_, v_x_531_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_570_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v___y_547_ = v___x_572_;
goto v___jp_546_;
}
}
}
default: 
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_x_530_);
lean_ctor_set(v___x_575_, 1, v_x_531_);
v___y_547_ = v___x_575_;
goto v___jp_546_;
}
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_array_fset(v_xs_x27_545_, v_j_537_, v___y_547_);
lean_dec(v_j_537_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_548_);
v___x_550_ = v___x_541_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_ks_578_; lean_object* v_vs_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_599_; 
v_ks_578_ = lean_ctor_get(v_x_527_, 0);
v_vs_579_ = lean_ctor_get(v_x_527_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_527_);
if (v_isSharedCheck_599_ == 0)
{
v___x_581_ = v_x_527_;
v_isShared_582_ = v_isSharedCheck_599_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_vs_579_);
lean_inc(v_ks_578_);
lean_dec(v_x_527_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_599_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ks_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_vs_579_);
v___x_584_ = v_reuseFailAlloc_598_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v_newNode_585_; uint8_t v___y_587_; size_t v___x_593_; uint8_t v___x_594_; 
v_newNode_585_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v___x_584_, v_x_530_, v_x_531_);
v___x_593_ = ((size_t)7ULL);
v___x_594_ = lean_usize_dec_le(v___x_593_, v_x_529_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_585_);
v___x_596_ = lean_unsigned_to_nat(4u);
v___x_597_ = lean_nat_dec_lt(v___x_595_, v___x_596_);
lean_dec(v___x_595_);
v___y_587_ = v___x_597_;
goto v___jp_586_;
}
else
{
v___y_587_ = v___x_594_;
goto v___jp_586_;
}
v___jp_586_:
{
if (v___y_587_ == 0)
{
lean_object* v_ks_588_; lean_object* v_vs_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_ks_588_ = lean_ctor_get(v_newNode_585_, 0);
lean_inc_ref(v_ks_588_);
v_vs_589_ = lean_ctor_get(v_newNode_585_, 1);
lean_inc_ref(v_vs_589_);
lean_dec_ref(v_newNode_585_);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_592_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_x_529_, v_ks_588_, v_vs_589_, v___x_590_, v___x_591_);
lean_dec_ref(v_vs_589_);
lean_dec_ref(v_ks_588_);
return v___x_592_;
}
else
{
return v_newNode_585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_600_, lean_object* v_keys_601_, lean_object* v_vals_602_, lean_object* v_i_603_, lean_object* v_entries_604_){
_start:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_get_size(v_keys_601_);
v___x_606_ = lean_nat_dec_lt(v_i_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_i_603_);
return v_entries_604_;
}
else
{
lean_object* v_k_607_; lean_object* v_v_608_; uint64_t v___x_609_; size_t v_h_610_; size_t v___x_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v_h_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_k_607_ = lean_array_fget_borrowed(v_keys_601_, v_i_603_);
v_v_608_ = lean_array_fget_borrowed(v_vals_602_, v_i_603_);
v___x_609_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_607_);
v_h_610_ = lean_uint64_to_usize(v___x_609_);
v___x_611_ = ((size_t)5ULL);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_sub(v_depth_600_, v___x_613_);
v___x_615_ = lean_usize_mul(v___x_611_, v___x_614_);
v_h_616_ = lean_usize_shift_right(v_h_610_, v___x_615_);
v___x_617_ = lean_nat_add(v_i_603_, v___x_612_);
lean_dec(v_i_603_);
lean_inc(v_v_608_);
lean_inc(v_k_607_);
v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_entries_604_, v_h_616_, v_depth_600_, v_k_607_, v_v_608_);
v_i_603_ = v___x_617_;
v_entries_604_ = v___x_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_620_, lean_object* v_keys_621_, lean_object* v_vals_622_, lean_object* v_i_623_, lean_object* v_entries_624_){
_start:
{
size_t v_depth_boxed_625_; lean_object* v_res_626_; 
v_depth_boxed_625_ = lean_unbox_usize(v_depth_620_);
lean_dec(v_depth_620_);
v_res_626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_625_, v_keys_621_, v_vals_622_, v_i_623_, v_entries_624_);
lean_dec_ref(v_vals_622_);
lean_dec_ref(v_keys_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_8276__boxed_632_; size_t v_x_8277__boxed_633_; lean_object* v_res_634_; 
v_x_8276__boxed_632_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_x_8277__boxed_633_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_res_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_627_, v_x_8276__boxed_632_, v_x_8277__boxed_633_, v_x_630_, v_x_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
uint64_t v___x_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_638_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_636_);
v___x_639_ = lean_uint64_to_usize(v___x_638_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_635_, v___x_639_, v___x_640_, v_x_636_, v_x_637_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_rings_645_; lean_object* v_typeIdOf_646_; lean_object* v_exprToRingId_647_; lean_object* v_semirings_648_; lean_object* v_stypeIdOf_649_; lean_object* v_exprToSemiringId_650_; lean_object* v_ncRings_651_; lean_object* v_exprToNCRingId_652_; lean_object* v_nctypeIdOf_653_; lean_object* v_ncSemirings_654_; lean_object* v_exprToNCSemiringId_655_; lean_object* v_ncstypeIdOf_656_; lean_object* v_steps_657_; uint8_t v_reportedMaxDegreeIssue_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_rings_645_ = lean_ctor_get(v_s_644_, 0);
v_typeIdOf_646_ = lean_ctor_get(v_s_644_, 1);
v_exprToRingId_647_ = lean_ctor_get(v_s_644_, 2);
v_semirings_648_ = lean_ctor_get(v_s_644_, 3);
v_stypeIdOf_649_ = lean_ctor_get(v_s_644_, 4);
v_exprToSemiringId_650_ = lean_ctor_get(v_s_644_, 5);
v_ncRings_651_ = lean_ctor_get(v_s_644_, 6);
v_exprToNCRingId_652_ = lean_ctor_get(v_s_644_, 7);
v_nctypeIdOf_653_ = lean_ctor_get(v_s_644_, 8);
v_ncSemirings_654_ = lean_ctor_get(v_s_644_, 9);
v_exprToNCSemiringId_655_ = lean_ctor_get(v_s_644_, 10);
v_ncstypeIdOf_656_ = lean_ctor_get(v_s_644_, 11);
v_steps_657_ = lean_ctor_get(v_s_644_, 12);
v_reportedMaxDegreeIssue_658_ = lean_ctor_get_uint8(v_s_644_, sizeof(void*)*13);
v_isSharedCheck_666_ = !lean_is_exclusive(v_s_644_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v_s_644_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_steps_657_);
lean_inc(v_ncstypeIdOf_656_);
lean_inc(v_exprToNCSemiringId_655_);
lean_inc(v_ncSemirings_654_);
lean_inc(v_nctypeIdOf_653_);
lean_inc(v_exprToNCRingId_652_);
lean_inc(v_ncRings_651_);
lean_inc(v_exprToSemiringId_650_);
lean_inc(v_stypeIdOf_649_);
lean_inc(v_semirings_648_);
lean_inc(v_exprToRingId_647_);
lean_inc(v_typeIdOf_646_);
lean_inc(v_rings_645_);
lean_dec(v_s_644_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc(v_a_643_);
v___x_662_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_exprToNCSemiringId_655_, v_e_642_, v_a_643_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 10, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_rings_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_typeIdOf_646_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_exprToRingId_647_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_semirings_648_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_stypeIdOf_649_);
lean_ctor_set(v_reuseFailAlloc_665_, 5, v_exprToSemiringId_650_);
lean_ctor_set(v_reuseFailAlloc_665_, 6, v_ncRings_651_);
lean_ctor_set(v_reuseFailAlloc_665_, 7, v_exprToNCRingId_652_);
lean_ctor_set(v_reuseFailAlloc_665_, 8, v_nctypeIdOf_653_);
lean_ctor_set(v_reuseFailAlloc_665_, 9, v_ncSemirings_654_);
lean_ctor_set(v_reuseFailAlloc_665_, 10, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 11, v_ncstypeIdOf_656_);
lean_ctor_set(v_reuseFailAlloc_665_, 12, v_steps_657_);
lean_ctor_set_uint8(v_reuseFailAlloc_665_, sizeof(void*)*13, v_reportedMaxDegreeIssue_658_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed(lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_s_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0(v_e_667_, v_a_668_, v_s_669_);
lean_dec(v_a_668_);
return v_res_670_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__0));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommSemiringId_x3f___redArg(v_e_674_, v_a_676_, v_a_681_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v___x_687_);
if (lean_obj_tag(v_a_688_) == 1)
{
lean_object* v_val_689_; uint8_t v___x_690_; 
v_val_689_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref(v_a_688_);
v___x_690_ = lean_nat_dec_eq(v_val_689_, v_a_675_);
lean_dec(v_val_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_677_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; uint8_t v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v___x_693_ = lean_unbox(v_a_692_);
lean_dec(v_a_692_);
if (v___x_693_ == 0)
{
lean_dec_ref(v_e_674_);
goto v___jp_684_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___closed__1);
v___x_695_ = l_Lean_indentExpr(v_e_674_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_Meta_Sym_reportIssue(v___x_696_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_dec_ref(v___x_697_);
goto v___jp_684_;
}
else
{
return v___x_697_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_e_674_);
v_a_698_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_691_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_691_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_dec_ref(v_e_674_);
goto v___jp_684_;
}
}
else
{
lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_a_688_);
lean_inc(v_a_675_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_706_, 0, v_e_674_);
lean_closure_set(v___f_706_, 1, v_a_675_);
v___x_707_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_708_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_707_, v___f_706_, v_a_676_);
return v___x_708_;
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_e_674_);
v_a_709_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_687_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_687_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg___boxed(lean_object* v_e_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec(v_a_718_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_728_, v_a_729_, v_a_730_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___boxed(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
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
lean_dec(v_a_743_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0(lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0___redArg(v_x_757_, v_x_758_, v_x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, size_t v_x_763_, size_t v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___redArg(v_x_762_, v_x_763_, v_x_764_, v_x_765_, v_x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
size_t v_x_8555__boxed_774_; size_t v_x_8556__boxed_775_; lean_object* v_res_776_; 
v_x_8555__boxed_774_ = lean_unbox_usize(v_x_770_);
lean_dec(v_x_770_);
v_x_8556__boxed_775_ = lean_unbox_usize(v_x_771_);
lean_dec(v_x_771_);
v_res_776_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0(v_00_u03b2_768_, v_x_769_, v_x_8555__boxed_774_, v_x_8556__boxed_775_, v_x_772_, v_x_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_777_, lean_object* v_n_778_, lean_object* v_k_779_, lean_object* v_v_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1___redArg(v_n_778_, v_k_779_, v_v_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_782_, size_t v_depth_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_heq_786_, lean_object* v_i_787_, lean_object* v_entries_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_783_, v_keys_784_, v_vals_785_, v_i_787_, v_entries_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_790_, lean_object* v_depth_791_, lean_object* v_keys_792_, lean_object* v_vals_793_, lean_object* v_heq_794_, lean_object* v_i_795_, lean_object* v_entries_796_){
_start:
{
size_t v_depth_boxed_797_; lean_object* v_res_798_; 
v_depth_boxed_797_ = lean_unbox_usize(v_depth_791_);
lean_dec(v_depth_791_);
v_res_798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_790_, v_depth_boxed_797_, v_keys_792_, v_vals_793_, v_heq_794_, v_i_795_, v_entries_796_);
lean_dec_ref(v_vals_793_);
lean_dec_ref(v_keys_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_800_, v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(lean_object* v_e_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_805_, v___y_806_, v___y_807_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0___boxed(lean_object* v_e_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommSemiringM___lam__0(v_e_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
return v_res_832_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
