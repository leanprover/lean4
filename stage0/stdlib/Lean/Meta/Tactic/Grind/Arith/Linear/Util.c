// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Util
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.Util import Init.Data.Int.Gcd
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
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "expression in two different structure in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "`grind linarith` internal error, structure does not implement `NoNatZeroDivisors`"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "`grind linarith` internal error, structure does not support LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "`grind linarith` internal error, structure does not support LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "`grind linarith` internal error, structure does not have a lawful LT instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`grind linarith` internal error, structure is not a preorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`grind linarith` internal error, structure is not a linear order"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "`grind linarith` internal error, structure is not a ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`grind linarith` internal error, structure is not a commutative ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`grind linarith` internal error, structure is not an ordered ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`grind linarith` internal error, unexpected constant polynomial"};
static const lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value;
static lean_once_cell_t l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_zero_18_; lean_object* v___x_20_; 
v_zero_18_ = lean_ctor_get(v_a_14_, 17);
lean_inc_ref(v_zero_18_);
lean_dec(v_a_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_zero_18_);
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_zero_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_a_23_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_13_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_13_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Grind_Arith_Linear_getZero(v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec(v_a_32_);
lean_dec(v_a_31_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_67_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_67_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_one_x3f_61_; 
v_one_x3f_61_ = lean_ctor_get(v_a_57_, 19);
lean_inc(v_one_x3f_61_);
lean_dec(v_a_57_);
if (lean_obj_tag(v_one_x3f_61_) == 1)
{
lean_object* v_val_62_; lean_object* v___x_64_; 
v_val_62_ = lean_ctor_get(v_one_x3f_61_, 0);
lean_inc(v_val_62_);
lean_dec_ref_known(v_one_x3f_61_, 1);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v_val_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_val_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v___x_66_; 
lean_dec(v_one_x3f_61_);
lean_del_object(v___x_59_);
v___x_66_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_66_;
}
}
}
else
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v_a_68_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v___x_56_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_56_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_Linear_getOne(v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec(v_a_77_);
lean_dec(v_a_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_117_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_117_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_117_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_117_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_ringId_x3f_106_; 
v_ringId_x3f_106_ = lean_ctor_get(v_a_102_, 1);
lean_inc(v_ringId_x3f_106_);
lean_dec(v_a_102_);
if (lean_obj_tag(v_ringId_x3f_106_) == 0)
{
uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = 0;
v___x_108_ = lean_box(v___x_107_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec_ref_known(v_ringId_x3f_106_, 1);
v___x_112_ = 1;
v___x_113_ = lean_box(v___x_112_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_113_);
v___x_115_ = v___x_104_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_101_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_101_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_153_) == 0)
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v_a_152_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_153_, 0);
lean_dec(v_unused_162_);
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_a_152_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_152_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_176_; 
v_a_163_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_176_ == 0)
{
v___x_165_ = v___x_153_;
v_isShared_166_ = v_isSharedCheck_176_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_153_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_176_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_orderedRingInst_x3f_167_; 
v_orderedRingInst_x3f_167_ = lean_ctor_get(v_a_163_, 14);
lean_inc(v_orderedRingInst_x3f_167_);
lean_dec(v_a_163_);
if (lean_obj_tag(v_orderedRingInst_x3f_167_) == 0)
{
uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec(v_a_152_);
v___x_168_ = 0;
v___x_169_ = lean_box(v___x_168_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_169_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec_ref_known(v_orderedRingInst_x3f_167_, 1);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v_a_152_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_152_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_152_);
v_a_177_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_153_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_153_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec(v_a_185_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_226_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_isLinearInst_x3f_215_; 
v_isLinearInst_x3f_215_ = lean_ctor_get(v_a_211_, 10);
lean_inc(v_isLinearInst_x3f_215_);
lean_dec(v_a_211_);
if (lean_obj_tag(v_isLinearInst_x3f_215_) == 0)
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = 0;
v___x_217_ = lean_box(v___x_216_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_217_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
else
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec_ref_known(v_isLinearInst_x3f_215_, 1);
v___x_221_ = 1;
v___x_222_ = lean_box(v___x_221_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_222_);
v___x_224_ = v___x_213_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_210_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_210_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_276_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_276_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_276_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_276_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_lawfulOrderLTInst_x3f_265_; 
v_lawfulOrderLTInst_x3f_265_ = lean_ctor_get(v_a_261_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_265_);
lean_dec(v_a_261_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_265_) == 0)
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = 0;
v___x_267_ = lean_box(v___x_266_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_267_);
v___x_269_ = v___x_263_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_265_, 1);
v___x_271_ = 1;
v___x_272_ = lean_box(v___x_271_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_272_);
v___x_274_ = v___x_263_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_260_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_260_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_Linear_hasLawfulLT(v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec(v_a_286_);
lean_dec(v_a_285_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_326_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_326_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_326_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_326_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_noNatDivInst_x3f_315_; 
v_noNatDivInst_x3f_315_ = lean_ctor_get(v_a_311_, 11);
lean_inc(v_noNatDivInst_x3f_315_);
lean_dec(v_a_311_);
if (lean_obj_tag(v_noNatDivInst_x3f_315_) == 0)
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = 0;
v___x_317_ = lean_box(v___x_316_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_317_);
v___x_319_ = v___x_313_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec_ref_known(v_noNatDivInst_x3f_315_, 1);
v___x_321_ = 1;
v___x_322_ = lean_box(v___x_321_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_322_);
v___x_324_ = v___x_313_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_310_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_310_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec(v_a_336_);
lean_dec(v_a_335_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_i_350_, lean_object* v_k_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_get_size(v_keys_348_);
v___x_353_ = lean_nat_dec_lt(v_i_350_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v_i_350_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
else
{
lean_object* v_k_x27_355_; size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v_k_x27_355_ = lean_array_fget_borrowed(v_keys_348_, v_i_350_);
v___x_356_ = lean_ptr_addr(v_k_351_);
v___x_357_ = lean_ptr_addr(v_k_x27_355_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_i_350_, v___x_359_);
lean_dec(v_i_350_);
v_i_350_ = v___x_360_;
goto _start;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_array_fget_borrowed(v_vals_349_, v_i_350_);
lean_dec(v_i_350_);
lean_inc(v___x_362_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_k_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_364_, v_vals_365_, v_i_366_, v_k_367_);
lean_dec_ref(v_k_367_);
lean_dec_ref(v_vals_365_);
lean_dec_ref(v_keys_364_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_369_, size_t v_x_370_, lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v_es_372_; lean_object* v___x_373_; size_t v___x_374_; size_t v___x_375_; lean_object* v_j_376_; lean_object* v___x_377_; 
v_es_372_ = lean_ctor_get(v_x_369_, 0);
v___x_373_ = lean_box(2);
v___x_374_ = ((size_t)31ULL);
v___x_375_ = lean_usize_land(v_x_370_, v___x_374_);
v_j_376_ = lean_usize_to_nat(v___x_375_);
v___x_377_ = lean_array_get_borrowed(v___x_373_, v_es_372_, v_j_376_);
lean_dec(v_j_376_);
switch(lean_obj_tag(v___x_377_))
{
case 0:
{
lean_object* v_key_378_; lean_object* v_val_379_; size_t v___x_380_; size_t v___x_381_; uint8_t v___x_382_; 
v_key_378_ = lean_ctor_get(v___x_377_, 0);
v_val_379_ = lean_ctor_get(v___x_377_, 1);
v___x_380_ = lean_ptr_addr(v_x_371_);
v___x_381_ = lean_ptr_addr(v_key_378_);
v___x_382_ = lean_usize_dec_eq(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
lean_inc(v_val_379_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v_val_379_);
return v___x_384_;
}
}
case 1:
{
lean_object* v_node_385_; size_t v___x_386_; size_t v___x_387_; 
v_node_385_ = lean_ctor_get(v___x_377_, 0);
v___x_386_ = ((size_t)5ULL);
v___x_387_ = lean_usize_shift_right(v_x_370_, v___x_386_);
v_x_369_ = v_node_385_;
v_x_370_ = v___x_387_;
goto _start;
}
default: 
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
}
else
{
lean_object* v_ks_390_; lean_object* v_vs_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_ks_390_ = lean_ctor_get(v_x_369_, 0);
v_vs_391_ = lean_ctor_get(v_x_369_, 1);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_390_, v_vs_391_, v___x_392_, v_x_371_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
size_t v_x_905__boxed_397_; lean_object* v_res_398_; 
v_x_905__boxed_397_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_res_398_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_394_, v_x_905__boxed_397_, v_x_396_);
lean_dec_ref(v_x_396_);
lean_dec_ref(v_x_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; uint64_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_401_ = lean_ptr_addr(v_x_400_);
v___x_402_ = ((size_t)3ULL);
v___x_403_ = lean_usize_shift_right(v___x_401_, v___x_402_);
v___x_404_ = lean_usize_to_uint64(v___x_403_);
v___x_405_ = lean_uint64_to_usize(v___x_404_);
v___x_406_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_399_, v___x_405_, v_x_400_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_407_, v_x_408_);
lean_dec_ref(v_x_408_);
lean_dec_ref(v_x_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_424_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_exprToStructId_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v_exprToStructId_419_ = lean_ctor_get(v_a_415_, 2);
lean_inc_ref(v_exprToStructId_419_);
lean_dec(v_a_415_);
v___x_420_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_419_, v_e_410_);
lean_dec_ref(v_exprToStructId_419_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
v_a_425_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_414_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_414_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_433_, v_a_434_, v_a_435_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_e_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_438_, v_a_439_, v_a_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_e_451_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_468_, v_x_469_, v_x_470_);
lean_dec_ref(v_x_470_);
lean_dec_ref(v_x_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, size_t v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_473_, v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
size_t v_x_1026__boxed_481_; lean_object* v_res_482_; 
v_x_1026__boxed_481_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_477_, v_x_478_, v_x_1026__boxed_481_, v_x_480_);
lean_dec_ref(v_x_480_);
lean_dec_ref(v_x_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_484_, v_vals_485_, v_i_487_, v_k_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_heq_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_490_, v_keys_491_, v_vals_492_, v_heq_493_, v_i_494_, v_k_495_);
lean_dec_ref(v_k_495_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_ks_501_; lean_object* v_vs_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_528_; 
v_ks_501_ = lean_ctor_get(v_x_497_, 0);
v_vs_502_ = lean_ctor_get(v_x_497_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_528_ == 0)
{
v___x_504_ = v_x_497_;
v_isShared_505_ = v_isSharedCheck_528_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_vs_502_);
lean_inc(v_ks_501_);
lean_dec(v_x_497_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_528_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_array_get_size(v_ks_501_);
v___x_507_ = lean_nat_dec_lt(v_x_498_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec(v_x_498_);
v___x_508_ = lean_array_push(v_ks_501_, v_x_499_);
v___x_509_ = lean_array_push(v_vs_502_, v_x_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_509_);
lean_ctor_set(v___x_504_, 0, v___x_508_);
v___x_511_ = v___x_504_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
else
{
lean_object* v_k_x27_513_; size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v_k_x27_513_ = lean_array_fget_borrowed(v_ks_501_, v_x_498_);
v___x_514_ = lean_ptr_addr(v_x_499_);
v___x_515_ = lean_ptr_addr(v_k_x27_513_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_518_; 
if (v_isShared_505_ == 0)
{
v___x_518_ = v___x_504_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_ks_501_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_vs_502_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_x_498_, v___x_519_);
lean_dec(v_x_498_);
v_x_497_ = v___x_518_;
v_x_498_ = v___x_520_;
goto _start;
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_523_ = lean_array_fset(v_ks_501_, v_x_498_, v_x_499_);
v___x_524_ = lean_array_fset(v_vs_502_, v_x_498_, v_x_500_);
lean_dec(v_x_498_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_524_);
lean_ctor_set(v___x_504_, 0, v___x_523_);
v___x_526_ = v___x_504_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_529_, lean_object* v_k_530_, lean_object* v_v_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_529_, v___x_532_, v_k_530_, v_v_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_535_, size_t v_x_536_, size_t v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
lean_object* v_es_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v_j_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_es_540_ = lean_ctor_get(v_x_535_, 0);
v___x_541_ = ((size_t)31ULL);
v___x_542_ = lean_usize_land(v_x_536_, v___x_541_);
v_j_543_ = lean_usize_to_nat(v___x_542_);
v___x_544_ = lean_array_get_size(v_es_540_);
v___x_545_ = lean_nat_dec_lt(v_j_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v_j_543_);
lean_dec(v_x_539_);
lean_dec_ref(v_x_538_);
return v_x_535_;
}
else
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_586_; 
lean_inc_ref(v_es_540_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_x_535_, 0);
lean_dec(v_unused_587_);
v___x_547_ = v_x_535_;
v_isShared_548_ = v_isSharedCheck_586_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_x_535_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_586_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_v_549_; lean_object* v___x_550_; lean_object* v_xs_x27_551_; lean_object* v___y_553_; 
v_v_549_ = lean_array_fget(v_es_540_, v_j_543_);
v___x_550_ = lean_box(0);
v_xs_x27_551_ = lean_array_fset(v_es_540_, v_j_543_, v___x_550_);
switch(lean_obj_tag(v_v_549_))
{
case 0:
{
lean_object* v_key_558_; lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_571_; 
v_key_558_ = lean_ctor_get(v_v_549_, 0);
v_val_559_ = lean_ctor_get(v_v_549_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_v_549_);
if (v_isSharedCheck_571_ == 0)
{
v___x_561_ = v_v_549_;
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_inc(v_key_558_);
lean_dec(v_v_549_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
size_t v___x_563_; size_t v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_ptr_addr(v_x_538_);
v___x_564_ = lean_ptr_addr(v_key_558_);
v___x_565_ = lean_usize_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_del_object(v___x_561_);
v___x_566_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_558_, v_val_559_, v_x_538_, v_x_539_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___y_553_ = v___x_567_;
goto v___jp_552_;
}
else
{
lean_object* v___x_569_; 
lean_dec(v_val_559_);
lean_dec(v_key_558_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_x_539_);
lean_ctor_set(v___x_561_, 0, v_x_538_);
v___x_569_ = v___x_561_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_x_538_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_x_539_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v___y_553_ = v___x_569_;
goto v___jp_552_;
}
}
}
}
case 1:
{
lean_object* v_node_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_node_572_ = lean_ctor_get(v_v_549_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_v_549_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_v_549_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_node_572_);
lean_dec(v_v_549_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_usize_shift_right(v_x_536_, v___x_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_x_537_, v___x_578_);
v___x_580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_572_, v___x_577_, v___x_579_, v_x_538_, v_x_539_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_580_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_553_ = v___x_582_;
goto v___jp_552_;
}
}
}
default: 
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_x_538_);
lean_ctor_set(v___x_585_, 1, v_x_539_);
v___y_553_ = v___x_585_;
goto v___jp_552_;
}
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_fset(v_xs_x27_551_, v_j_543_, v___y_553_);
lean_dec(v_j_543_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_554_);
v___x_556_ = v___x_547_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v_ks_588_; lean_object* v_vs_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_607_; 
v_ks_588_ = lean_ctor_get(v_x_535_, 0);
v_vs_589_ = lean_ctor_get(v_x_535_, 1);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_607_ == 0)
{
v___x_591_ = v_x_535_;
v_isShared_592_ = v_isSharedCheck_607_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_vs_589_);
lean_inc(v_ks_588_);
lean_dec(v_x_535_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_607_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_ks_588_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_vs_589_);
v___x_594_ = v_reuseFailAlloc_606_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v_newNode_595_; size_t v___x_596_; uint8_t v___x_597_; 
v_newNode_595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_594_, v_x_538_, v_x_539_);
v___x_596_ = ((size_t)7ULL);
v___x_597_ = lean_usize_dec_le(v___x_596_, v_x_537_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_595_);
v___x_599_ = lean_unsigned_to_nat(4u);
v___x_600_ = lean_nat_dec_lt(v___x_598_, v___x_599_);
lean_dec(v___x_598_);
if (v___x_600_ == 0)
{
lean_object* v_ks_601_; lean_object* v_vs_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_ks_601_ = lean_ctor_get(v_newNode_595_, 0);
lean_inc_ref(v_ks_601_);
v_vs_602_ = lean_ctor_get(v_newNode_595_, 1);
lean_inc_ref(v_vs_602_);
lean_dec_ref(v_newNode_595_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_537_, v_ks_601_, v_vs_602_, v___x_603_, v___x_604_);
lean_dec_ref(v_vs_602_);
lean_dec_ref(v_ks_601_);
return v___x_605_;
}
else
{
return v_newNode_595_;
}
}
else
{
return v_newNode_595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_i_611_, lean_object* v_entries_612_){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_keys_609_);
v___x_614_ = lean_nat_dec_lt(v_i_611_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v_i_611_);
return v_entries_612_;
}
else
{
lean_object* v_k_615_; lean_object* v_v_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; uint64_t v___x_620_; size_t v_h_621_; size_t v___x_622_; lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v_h_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_k_615_ = lean_array_fget_borrowed(v_keys_609_, v_i_611_);
v_v_616_ = lean_array_fget_borrowed(v_vals_610_, v_i_611_);
v___x_617_ = lean_ptr_addr(v_k_615_);
v___x_618_ = ((size_t)3ULL);
v___x_619_ = lean_usize_shift_right(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_to_uint64(v___x_619_);
v_h_621_ = lean_uint64_to_usize(v___x_620_);
v___x_622_ = ((size_t)5ULL);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_sub(v_depth_608_, v___x_624_);
v___x_626_ = lean_usize_mul(v___x_622_, v___x_625_);
v_h_627_ = lean_usize_shift_right(v_h_621_, v___x_626_);
v___x_628_ = lean_nat_add(v_i_611_, v___x_623_);
lean_dec(v_i_611_);
lean_inc(v_v_616_);
lean_inc(v_k_615_);
v___x_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_612_, v_h_627_, v_depth_608_, v_k_615_, v_v_616_);
v_i_611_ = v___x_628_;
v_entries_612_ = v___x_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_631_, lean_object* v_keys_632_, lean_object* v_vals_633_, lean_object* v_i_634_, lean_object* v_entries_635_){
_start:
{
size_t v_depth_boxed_636_; lean_object* v_res_637_; 
v_depth_boxed_636_ = lean_unbox_usize(v_depth_631_);
lean_dec(v_depth_631_);
v_res_637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_636_, v_keys_632_, v_vals_633_, v_i_634_, v_entries_635_);
lean_dec_ref(v_vals_633_);
lean_dec_ref(v_keys_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
size_t v_x_6468__boxed_643_; size_t v_x_6469__boxed_644_; lean_object* v_res_645_; 
v_x_6468__boxed_643_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_x_6469__boxed_644_ = lean_unbox_usize(v_x_640_);
lean_dec(v_x_640_);
v_res_645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_638_, v_x_6468__boxed_643_, v_x_6469__boxed_644_, v_x_641_, v_x_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; uint64_t v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_649_ = lean_ptr_addr(v_x_647_);
v___x_650_ = ((size_t)3ULL);
v___x_651_ = lean_usize_shift_right(v___x_649_, v___x_650_);
v___x_652_ = lean_usize_to_uint64(v___x_651_);
v___x_653_ = lean_uint64_to_usize(v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_646_, v___x_653_, v___x_654_, v_x_647_, v_x_648_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_656_, lean_object* v_a_657_, lean_object* v_s_658_){
_start:
{
lean_object* v_structs_659_; lean_object* v_typeIdOf_660_; lean_object* v_exprToStructId_661_; lean_object* v_exprToStructIdEntries_662_; lean_object* v_forbiddenNatModules_663_; lean_object* v_natStructs_664_; lean_object* v_natTypeIdOf_665_; lean_object* v_exprToNatStructId_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_structs_659_ = lean_ctor_get(v_s_658_, 0);
v_typeIdOf_660_ = lean_ctor_get(v_s_658_, 1);
v_exprToStructId_661_ = lean_ctor_get(v_s_658_, 2);
v_exprToStructIdEntries_662_ = lean_ctor_get(v_s_658_, 3);
v_forbiddenNatModules_663_ = lean_ctor_get(v_s_658_, 4);
v_natStructs_664_ = lean_ctor_get(v_s_658_, 5);
v_natTypeIdOf_665_ = lean_ctor_get(v_s_658_, 6);
v_exprToNatStructId_666_ = lean_ctor_get(v_s_658_, 7);
v_isSharedCheck_676_ = !lean_is_exclusive(v_s_658_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v_s_658_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_exprToNatStructId_666_);
lean_inc(v_natTypeIdOf_665_);
lean_inc(v_natStructs_664_);
lean_inc(v_forbiddenNatModules_663_);
lean_inc(v_exprToStructIdEntries_662_);
lean_inc(v_exprToStructId_661_);
lean_inc(v_typeIdOf_660_);
lean_inc(v_structs_659_);
lean_dec(v_s_658_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
lean_inc_n(v_a_657_, 2);
lean_inc_ref(v_e_656_);
v___x_670_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_661_, v_e_656_, v_a_657_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_e_656_);
lean_ctor_set(v___x_671_, 1, v_a_657_);
v___x_672_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_662_, v___x_671_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 3, v___x_672_);
lean_ctor_set(v___x_668_, 2, v___x_670_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_structs_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_typeIdOf_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_forbiddenNatModules_663_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v_natStructs_664_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_natTypeIdOf_665_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v_exprToNatStructId_666_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_677_, v_a_678_, v_s_679_);
lean_dec(v_a_678_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
lean_inc(v_a_685_);
lean_inc_ref(v_e_684_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_697_, 0, v_e_684_);
lean_closure_set(v___f_697_, 1, v_a_685_);
v___x_698_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_684_, v_a_686_, v_a_691_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
if (lean_obj_tag(v_a_699_) == 1)
{
lean_object* v_val_700_; uint8_t v___x_701_; 
lean_dec_ref(v___f_697_);
v_val_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_a_699_, 1);
v___x_701_ = lean_nat_dec_eq(v_val_700_, v_a_685_);
lean_dec(v_val_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_703_ = l_Lean_indentExpr(v_e_684_);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_687_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; uint8_t v_verbose_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v_verbose_707_ = lean_ctor_get_uint8(v_a_706_, 0);
lean_dec(v_a_706_);
if (v_verbose_707_ == 0)
{
lean_dec_ref_known(v___x_704_, 2);
goto v___jp_694_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_Sym_reportIssue(v___x_704_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_dec_ref_known(v___x_708_, 1);
goto v___jp_694_;
}
else
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref_known(v___x_704_, 2);
v_a_709_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_705_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_705_);
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
}
else
{
lean_dec_ref(v_e_684_);
goto v___jp_694_;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_a_699_);
lean_dec_ref(v_e_684_);
v___x_717_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_717_, v___f_697_, v_a_686_);
return v___x_718_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v___f_697_);
lean_dec_ref(v_e_684_);
v_a_719_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_698_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_698_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_738_, v_a_739_, v_a_740_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_767_, v_x_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_771_, lean_object* v_x_772_, size_t v_x_773_, size_t v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_772_, v_x_773_, v_x_774_, v_x_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
size_t v_x_6758__boxed_784_; size_t v_x_6759__boxed_785_; lean_object* v_res_786_; 
v_x_6758__boxed_784_ = lean_unbox_usize(v_x_780_);
lean_dec(v_x_780_);
v_x_6759__boxed_785_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_778_, v_x_779_, v_x_6758__boxed_784_, v_x_6759__boxed_785_, v_x_782_, v_x_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_787_, lean_object* v_n_788_, lean_object* v_k_789_, lean_object* v_v_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_788_, v_k_789_, v_v_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_792_, size_t v_depth_793_, lean_object* v_keys_794_, lean_object* v_vals_795_, lean_object* v_heq_796_, lean_object* v_i_797_, lean_object* v_entries_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_793_, v_keys_794_, v_vals_795_, v_i_797_, v_entries_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_800_, lean_object* v_depth_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_entries_806_){
_start:
{
size_t v_depth_boxed_807_; lean_object* v_res_808_; 
v_depth_boxed_807_ = lean_unbox_usize(v_depth_801_);
lean_dec(v_depth_801_);
v_res_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_800_, v_depth_boxed_807_, v_keys_802_, v_vals_803_, v_heq_804_, v_i_805_, v_entries_806_);
lean_dec_ref(v_vals_803_);
lean_dec_ref(v_keys_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_810_, v_x_811_, v_x_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v_env_822_; uint8_t v___x_823_; lean_object* v_env_824_; lean_object* v___x_825_; lean_object* v_toCold_826_; lean_object* v_mctx_827_; lean_object* v_lctx_828_; lean_object* v_options_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_821_ = lean_st_ref_get(v___y_819_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = 0;
v_env_824_ = l_Lean_Environment_setRecordingDeps(v_env_822_, v___x_823_);
v___x_825_ = lean_st_ref_get(v___y_817_);
v_toCold_826_ = lean_ctor_get(v___y_818_, 0);
v_mctx_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc_ref(v_mctx_827_);
lean_dec(v___x_825_);
v_lctx_828_ = lean_ctor_get(v___y_816_, 2);
v_options_829_ = lean_ctor_get(v_toCold_826_, 2);
lean_inc_ref(v_options_829_);
lean_inc_ref(v_lctx_828_);
v___x_830_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_830_, 0, v_env_824_);
lean_ctor_set(v___x_830_, 1, v_mctx_827_);
lean_ctor_set(v___x_830_, 2, v_lctx_828_);
lean_ctor_set(v___x_830_, 3, v_options_829_);
v___x_831_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_msgData_815_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_ref_846_; lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_ref_846_ = lean_ctor_get(v___y_843_, 2);
v___x_847_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_inc(v_ref_846_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_ref_846_);
lean_ctor_set(v___x_852_, 1, v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 1);
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_891_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_891_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_noNatDivInst_x3f_884_; 
v_noNatDivInst_x3f_884_ = lean_ctor_get(v_a_880_, 11);
lean_inc(v_noNatDivInst_x3f_884_);
lean_dec(v_a_880_);
if (lean_obj_tag(v_noNatDivInst_x3f_884_) == 1)
{
lean_object* v_val_885_; lean_object* v___x_887_; 
v_val_885_ = lean_ctor_get(v_noNatDivInst_x3f_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_noNatDivInst_x3f_884_, 1);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_val_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_val_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_noNatDivInst_x3f_884_);
lean_del_object(v___x_882_);
v___x_889_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_890_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_889_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
return v___x_890_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_879_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_879_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_a_900_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_914_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_928_, lean_object* v_msg_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_928_, v_msg_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
return v_res_942_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_970_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_970_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_leInst_x3f_963_; 
v_leInst_x3f_963_ = lean_ctor_get(v_a_959_, 5);
lean_inc(v_leInst_x3f_963_);
lean_dec(v_a_959_);
if (lean_obj_tag(v_leInst_x3f_963_) == 1)
{
lean_object* v_val_964_; lean_object* v___x_966_; 
v_val_964_ = lean_ctor_get(v_leInst_x3f_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v_leInst_x3f_963_, 1);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_val_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_val_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_leInst_x3f_963_);
lean_del_object(v___x_961_);
v___x_968_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_969_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_968_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_969_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_a_971_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_958_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_958_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec(v_a_979_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1019_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1019_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1019_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_ltInst_x3f_1012_; 
v_ltInst_x3f_1012_ = lean_ctor_get(v_a_1008_, 6);
lean_inc(v_ltInst_x3f_1012_);
lean_dec(v_a_1008_);
if (lean_obj_tag(v_ltInst_x3f_1012_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; 
v_val_1013_ = lean_ctor_get(v_ltInst_x3f_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_ltInst_x3f_1012_, 1);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_val_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_val_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_ltInst_x3f_1012_);
lean_del_object(v___x_1010_);
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_1018_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1017_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1007_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1007_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec(v_a_1028_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1068_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_lawfulOrderLTInst_x3f_1061_; 
v_lawfulOrderLTInst_x3f_1061_ = lean_ctor_get(v_a_1057_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1061_);
lean_dec(v_a_1057_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1061_) == 1)
{
lean_object* v_val_1062_; lean_object* v___x_1064_; 
v_val_1062_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1061_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1061_, 1);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_val_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_val_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_lawfulOrderLTInst_x3f_1061_);
lean_del_object(v___x_1059_);
v___x_1066_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1067_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1066_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1056_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1056_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1117_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1117_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_isPreorderInst_x3f_1110_; 
v_isPreorderInst_x3f_1110_ = lean_ctor_get(v_a_1106_, 8);
lean_inc(v_isPreorderInst_x3f_1110_);
lean_dec(v_a_1106_);
if (lean_obj_tag(v_isPreorderInst_x3f_1110_) == 1)
{
lean_object* v_val_1111_; lean_object* v___x_1113_; 
v_val_1111_ = lean_ctor_get(v_isPreorderInst_x3f_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v_isPreorderInst_x3f_1110_, 1);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_val_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_val_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_isPreorderInst_x3f_1110_);
lean_del_object(v___x_1108_);
v___x_1115_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1116_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1115_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1105_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1105_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1138_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1166_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_orderedAddInst_x3f_1159_; 
v_orderedAddInst_x3f_1159_ = lean_ctor_get(v_a_1155_, 9);
lean_inc(v_orderedAddInst_x3f_1159_);
lean_dec(v_a_1155_);
if (lean_obj_tag(v_orderedAddInst_x3f_1159_) == 1)
{
lean_object* v_val_1160_; lean_object* v___x_1162_; 
v_val_1160_ = lean_ctor_get(v_orderedAddInst_x3f_1159_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v_orderedAddInst_x3f_1159_, 1);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_val_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_val_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec(v_orderedAddInst_x3f_1159_);
lean_del_object(v___x_1157_);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1165_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1164_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1154_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1154_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec(v_a_1175_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1216_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1216_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1216_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_orderedAddInst_x3f_1205_; 
v_orderedAddInst_x3f_1205_ = lean_ctor_get(v_a_1201_, 9);
lean_inc(v_orderedAddInst_x3f_1205_);
lean_dec(v_a_1201_);
if (lean_obj_tag(v_orderedAddInst_x3f_1205_) == 0)
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = 0;
v___x_1207_ = lean_box(v___x_1206_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
else
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec_ref_known(v_orderedAddInst_x3f_1205_, 1);
v___x_1211_ = 1;
v___x_1212_ = lean_box(v___x_1211_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1212_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
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
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_a_1217_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1200_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1200_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec(v_a_1225_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_____do__lift_1241_){
_start:
{
lean_object* v_ltFn_x3f_1242_; 
v_ltFn_x3f_1242_ = lean_ctor_get(v_____do__lift_1241_, 21);
lean_inc(v_ltFn_x3f_1242_);
lean_dec_ref(v_____do__lift_1241_);
if (lean_obj_tag(v_ltFn_x3f_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
v_val_1243_ = lean_ctor_get(v_ltFn_x3f_1242_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v_ltFn_x3f_1242_, 1);
v___x_1244_ = lean_apply_2(v_toPure_1238_, lean_box(0), v_val_1243_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_ltFn_x3f_1242_);
lean_dec(v_toPure_1238_);
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1246_ = l_Lean_throwError___redArg(v_inst_1239_, v_inst_1240_, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_){
_start:
{
lean_object* v_toApplicative_1250_; lean_object* v_toBind_1251_; lean_object* v_toPure_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; 
v_toApplicative_1250_ = lean_ctor_get(v_inst_1247_, 0);
v_toBind_1251_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc(v_toBind_1251_);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1250_, 1);
lean_inc(v_toPure_1252_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1253_, 0, v_toPure_1252_);
lean_closure_set(v___f_1253_, 1, v_inst_1247_);
lean_closure_set(v___f_1253_, 2, v_inst_1248_);
v___x_1254_ = lean_apply_4(v_toBind_1251_, lean_box(0), lean_box(0), v_inst_1249_, v___f_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1256_, v_inst_1257_, v_inst_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_____do__lift_1266_){
_start:
{
lean_object* v_leFn_x3f_1267_; 
v_leFn_x3f_1267_ = lean_ctor_get(v_____do__lift_1266_, 20);
lean_inc(v_leFn_x3f_1267_);
lean_dec_ref(v_____do__lift_1266_);
if (lean_obj_tag(v_leFn_x3f_1267_) == 1)
{
lean_object* v_val_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_inst_1265_);
lean_dec_ref(v_inst_1264_);
v_val_1268_ = lean_ctor_get(v_leFn_x3f_1267_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v_leFn_x3f_1267_, 1);
v___x_1269_ = lean_apply_2(v_toPure_1263_, lean_box(0), v_val_1268_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_leFn_x3f_1267_);
lean_dec(v_toPure_1263_);
v___x_1270_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1271_ = l_Lean_throwError___redArg(v_inst_1264_, v_inst_1265_, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_){
_start:
{
lean_object* v_toApplicative_1275_; lean_object* v_toBind_1276_; lean_object* v_toPure_1277_; lean_object* v___f_1278_; lean_object* v___x_1279_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1272_, 0);
v_toBind_1276_ = lean_ctor_get(v_inst_1272_, 1);
lean_inc(v_toBind_1276_);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1275_, 1);
lean_inc(v_toPure_1277_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1278_, 0, v_toPure_1277_);
lean_closure_set(v___f_1278_, 1, v_inst_1272_);
lean_closure_set(v___f_1278_, 2, v_inst_1273_);
v___x_1279_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v_inst_1274_, v___f_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1281_, v_inst_1282_, v_inst_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1312_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1312_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_isLinearInst_x3f_1305_; 
v_isLinearInst_x3f_1305_ = lean_ctor_get(v_a_1301_, 10);
lean_inc(v_isLinearInst_x3f_1305_);
lean_dec(v_a_1301_);
if (lean_obj_tag(v_isLinearInst_x3f_1305_) == 1)
{
lean_object* v_val_1306_; lean_object* v___x_1308_; 
v_val_1306_ = lean_ctor_get(v_isLinearInst_x3f_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v_isLinearInst_x3f_1305_, 1);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v_val_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_val_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_isLinearInst_x3f_1305_);
lean_del_object(v___x_1303_);
v___x_1310_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1311_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1310_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1300_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1300_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec(v_a_1321_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_ringInst_x3f_1354_; 
v_ringInst_x3f_1354_ = lean_ctor_get(v_a_1350_, 12);
lean_inc(v_ringInst_x3f_1354_);
lean_dec(v_a_1350_);
if (lean_obj_tag(v_ringInst_x3f_1354_) == 1)
{
lean_object* v_val_1355_; lean_object* v___x_1357_; 
v_val_1355_ = lean_ctor_get(v_ringInst_x3f_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v_ringInst_x3f_1354_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_val_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_val_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_ringInst_x3f_1354_);
lean_del_object(v___x_1352_);
v___x_1359_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1360_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1359_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1349_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1349_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec(v_a_1370_);
return v_res_1382_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1410_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1410_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1410_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_commRingInst_x3f_1403_; 
v_commRingInst_x3f_1403_ = lean_ctor_get(v_a_1399_, 13);
lean_inc(v_commRingInst_x3f_1403_);
lean_dec(v_a_1399_);
if (lean_obj_tag(v_commRingInst_x3f_1403_) == 1)
{
lean_object* v_val_1404_; lean_object* v___x_1406_; 
v_val_1404_ = lean_ctor_get(v_commRingInst_x3f_1403_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_commRingInst_x3f_1403_, 1);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v_val_1404_);
v___x_1406_ = v___x_1401_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_val_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v_commRingInst_x3f_1403_);
lean_del_object(v___x_1401_);
v___x_1408_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1409_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1408_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1398_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1398_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec(v_a_1419_);
return v_res_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1459_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1459_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1459_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_orderedRingInst_x3f_1452_; 
v_orderedRingInst_x3f_1452_ = lean_ctor_get(v_a_1448_, 14);
lean_inc(v_orderedRingInst_x3f_1452_);
lean_dec(v_a_1448_);
if (lean_obj_tag(v_orderedRingInst_x3f_1452_) == 1)
{
lean_object* v_val_1453_; lean_object* v___x_1455_; 
v_val_1453_ = lean_ctor_get(v_orderedRingInst_x3f_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v_orderedRingInst_x3f_1452_, 1);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v_val_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_val_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_orderedRingInst_x3f_1452_);
lean_del_object(v___x_1450_);
v___x_1457_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1458_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1457_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1447_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1447_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec(v_a_1468_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Rat_ofInt(v_a_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1483_, lean_object* v_v_1484_, lean_object* v_a_1485_){
_start:
{
if (lean_obj_tag(v_a_1485_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_v_1484_);
return v___x_1486_;
}
else
{
lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v_p_1489_; lean_object* v_size_1490_; uint8_t v___x_1491_; 
v_k_1487_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_k_1487_);
v_v_1488_ = lean_ctor_get(v_a_1485_, 1);
lean_inc(v_v_1488_);
v_p_1489_ = lean_ctor_get(v_a_1485_, 2);
lean_inc(v_p_1489_);
lean_dec_ref_known(v_a_1485_, 3);
v_size_1490_ = lean_ctor_get(v_a_1483_, 2);
v___x_1491_ = lean_nat_dec_lt(v_v_1488_, v_size_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec(v_p_1489_);
lean_dec(v_v_1488_);
lean_dec(v_k_1487_);
lean_dec_ref(v_v_1484_);
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = l_instInhabitedRat;
v___x_1494_ = l_Rat_ofInt(v_k_1487_);
v___x_1495_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1493_, v_a_1483_, v_v_1488_);
lean_dec(v_v_1488_);
v___x_1496_ = l_Rat_mul(v___x_1494_, v___x_1495_);
lean_dec_ref(v___x_1494_);
v___x_1497_ = l_Rat_add(v_v_1484_, v___x_1496_);
v_v_1484_ = v___x_1497_;
v_a_1485_ = v_p_1489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1499_, lean_object* v_v_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1499_, v_v_1500_, v_a_1501_);
lean_dec_ref(v_a_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_nat_to_int(v_a_1503_);
v___x_1505_ = l_Rat_ofInt(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1532_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1532_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1532_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_assignment_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v_assignment_1526_ = lean_ctor_get(v_a_1522_, 35);
lean_inc_ref(v_assignment_1526_);
lean_dec(v_a_1522_);
v___x_1527_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1526_, v___x_1527_, v_p_1508_);
lean_dec_ref(v_assignment_1526_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1528_);
v___x_1530_ = v___x_1524_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_p_1508_);
v_a_1533_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1521_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1521_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec(v_a_1542_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_nat_to_int(v_a_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_p_1570_; uint8_t v_strict_1571_; lean_object* v___x_1572_; 
v_p_1570_ = lean_ctor_get(v_c_1557_, 0);
lean_inc(v_p_1570_);
v_strict_1571_ = lean_ctor_get_uint8(v_c_1557_, sizeof(void*)*2);
lean_dec_ref(v_c_1557_);
v___x_1572_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1570_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1598_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1598_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1598_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
if (lean_obj_tag(v_a_1573_) == 1)
{
if (v_strict_1571_ == 0)
{
lean_object* v_val_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v_val_1577_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v_a_1573_, 1);
v___x_1578_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1579_ = l_Rat_instDecidableLe(v_val_1577_, v___x_1578_);
v___x_1580_ = l_Lean_Bool_toLBool(v___x_1579_);
v___x_1581_ = lean_box(v___x_1580_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1581_);
v___x_1583_ = v___x_1575_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
lean_object* v_val_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_val_1585_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_a_1573_, 1);
v___x_1586_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1587_ = l_Rat_blt(v_val_1585_, v___x_1586_);
v___x_1588_ = l_Lean_Bool_toLBool(v___x_1587_);
v___x_1589_ = lean_box(v___x_1588_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1589_);
v___x_1591_ = v___x_1575_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_a_1573_);
v___x_1593_ = 2;
v___x_1594_ = lean_box(v___x_1593_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1594_);
v___x_1596_ = v___x_1575_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1572_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1572_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_p_1634_; lean_object* v___x_1635_; 
v_p_1634_ = lean_ctor_get(v_c_1621_, 0);
lean_inc(v_p_1634_);
lean_dec_ref(v_c_1621_);
v___x_1635_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1634_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1655_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1655_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1655_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
uint8_t v___y_1641_; 
if (lean_obj_tag(v_a_1636_) == 1)
{
lean_object* v_val_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_val_1647_ = lean_ctor_get(v_a_1636_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v_a_1636_, 1);
v___x_1648_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1649_ = l_instDecidableEqRat_decEq(v_val_1647_, v___x_1648_);
lean_dec(v_val_1647_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; 
v___x_1650_ = 1;
v___y_1641_ = v___x_1650_;
goto v___jp_1640_;
}
else
{
uint8_t v___x_1651_; 
v___x_1651_ = 0;
v___y_1641_ = v___x_1651_;
goto v___jp_1640_;
}
}
else
{
uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_del_object(v___x_1638_);
lean_dec(v_a_1636_);
v___x_1652_ = 2;
v___x_1653_ = lean_box(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
v___jp_1640_:
{
uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = l_Lean_Bool_toLBool(v___y_1641_);
v___x_1643_ = lean_box(v___x_1642_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1643_);
v___x_1645_ = v___x_1638_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1635_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1635_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1678_, lean_object* v_x_1679_, lean_object* v_s_1680_){
_start:
{
lean_object* v_structs_1681_; lean_object* v_typeIdOf_1682_; lean_object* v_exprToStructId_1683_; lean_object* v_exprToStructIdEntries_1684_; lean_object* v_forbiddenNatModules_1685_; lean_object* v_natStructs_1686_; lean_object* v_natTypeIdOf_1687_; lean_object* v_exprToNatStructId_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_structs_1681_ = lean_ctor_get(v_s_1680_, 0);
v_typeIdOf_1682_ = lean_ctor_get(v_s_1680_, 1);
v_exprToStructId_1683_ = lean_ctor_get(v_s_1680_, 2);
v_exprToStructIdEntries_1684_ = lean_ctor_get(v_s_1680_, 3);
v_forbiddenNatModules_1685_ = lean_ctor_get(v_s_1680_, 4);
v_natStructs_1686_ = lean_ctor_get(v_s_1680_, 5);
v_natTypeIdOf_1687_ = lean_ctor_get(v_s_1680_, 6);
v_exprToNatStructId_1688_ = lean_ctor_get(v_s_1680_, 7);
v___x_1689_ = lean_array_get_size(v_structs_1681_);
v___x_1690_ = lean_nat_dec_lt(v_a_1678_, v___x_1689_);
if (v___x_1690_ == 0)
{
return v_s_1680_;
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1752_; 
lean_inc_ref(v_exprToNatStructId_1688_);
lean_inc_ref(v_natTypeIdOf_1687_);
lean_inc_ref(v_natStructs_1686_);
lean_inc_ref(v_forbiddenNatModules_1685_);
lean_inc_ref(v_exprToStructIdEntries_1684_);
lean_inc_ref(v_exprToStructId_1683_);
lean_inc_ref(v_typeIdOf_1682_);
lean_inc_ref(v_structs_1681_);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_s_1680_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1753_ = lean_ctor_get(v_s_1680_, 7);
lean_dec(v_unused_1753_);
v_unused_1754_ = lean_ctor_get(v_s_1680_, 6);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_s_1680_, 5);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_s_1680_, 4);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_s_1680_, 3);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_s_1680_, 2);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_s_1680_, 1);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_s_1680_, 0);
lean_dec(v_unused_1760_);
v___x_1692_ = v_s_1680_;
v_isShared_1693_ = v_isSharedCheck_1752_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_s_1680_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1752_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_v_1694_; lean_object* v_id_1695_; lean_object* v_ringId_x3f_1696_; lean_object* v_type_1697_; lean_object* v_u_1698_; lean_object* v_intModuleInst_1699_; lean_object* v_leInst_x3f_1700_; lean_object* v_ltInst_x3f_1701_; lean_object* v_lawfulOrderLTInst_x3f_1702_; lean_object* v_isPreorderInst_x3f_1703_; lean_object* v_orderedAddInst_x3f_1704_; lean_object* v_isLinearInst_x3f_1705_; lean_object* v_noNatDivInst_x3f_1706_; lean_object* v_ringInst_x3f_1707_; lean_object* v_commRingInst_x3f_1708_; lean_object* v_orderedRingInst_x3f_1709_; lean_object* v_fieldInst_x3f_1710_; lean_object* v_charInst_x3f_1711_; lean_object* v_zero_1712_; lean_object* v_ofNatZero_1713_; lean_object* v_one_x3f_1714_; lean_object* v_leFn_x3f_1715_; lean_object* v_ltFn_x3f_1716_; lean_object* v_addFn_1717_; lean_object* v_zsmulFn_1718_; lean_object* v_nsmulFn_1719_; lean_object* v_zsmulFn_x3f_1720_; lean_object* v_nsmulFn_x3f_1721_; lean_object* v_homomulFn_x3f_1722_; lean_object* v_subFn_1723_; lean_object* v_negFn_1724_; lean_object* v_vars_1725_; lean_object* v_varMap_1726_; lean_object* v_lowers_1727_; lean_object* v_uppers_1728_; lean_object* v_diseqs_1729_; lean_object* v_assignment_1730_; uint8_t v_caseSplits_1731_; lean_object* v_conflict_x3f_1732_; lean_object* v_diseqSplits_1733_; lean_object* v_elimEqs_1734_; lean_object* v_elimStack_1735_; lean_object* v_occurs_1736_; lean_object* v_ignored_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1751_; 
v_v_1694_ = lean_array_fget(v_structs_1681_, v_a_1678_);
v_id_1695_ = lean_ctor_get(v_v_1694_, 0);
v_ringId_x3f_1696_ = lean_ctor_get(v_v_1694_, 1);
v_type_1697_ = lean_ctor_get(v_v_1694_, 2);
v_u_1698_ = lean_ctor_get(v_v_1694_, 3);
v_intModuleInst_1699_ = lean_ctor_get(v_v_1694_, 4);
v_leInst_x3f_1700_ = lean_ctor_get(v_v_1694_, 5);
v_ltInst_x3f_1701_ = lean_ctor_get(v_v_1694_, 6);
v_lawfulOrderLTInst_x3f_1702_ = lean_ctor_get(v_v_1694_, 7);
v_isPreorderInst_x3f_1703_ = lean_ctor_get(v_v_1694_, 8);
v_orderedAddInst_x3f_1704_ = lean_ctor_get(v_v_1694_, 9);
v_isLinearInst_x3f_1705_ = lean_ctor_get(v_v_1694_, 10);
v_noNatDivInst_x3f_1706_ = lean_ctor_get(v_v_1694_, 11);
v_ringInst_x3f_1707_ = lean_ctor_get(v_v_1694_, 12);
v_commRingInst_x3f_1708_ = lean_ctor_get(v_v_1694_, 13);
v_orderedRingInst_x3f_1709_ = lean_ctor_get(v_v_1694_, 14);
v_fieldInst_x3f_1710_ = lean_ctor_get(v_v_1694_, 15);
v_charInst_x3f_1711_ = lean_ctor_get(v_v_1694_, 16);
v_zero_1712_ = lean_ctor_get(v_v_1694_, 17);
v_ofNatZero_1713_ = lean_ctor_get(v_v_1694_, 18);
v_one_x3f_1714_ = lean_ctor_get(v_v_1694_, 19);
v_leFn_x3f_1715_ = lean_ctor_get(v_v_1694_, 20);
v_ltFn_x3f_1716_ = lean_ctor_get(v_v_1694_, 21);
v_addFn_1717_ = lean_ctor_get(v_v_1694_, 22);
v_zsmulFn_1718_ = lean_ctor_get(v_v_1694_, 23);
v_nsmulFn_1719_ = lean_ctor_get(v_v_1694_, 24);
v_zsmulFn_x3f_1720_ = lean_ctor_get(v_v_1694_, 25);
v_nsmulFn_x3f_1721_ = lean_ctor_get(v_v_1694_, 26);
v_homomulFn_x3f_1722_ = lean_ctor_get(v_v_1694_, 27);
v_subFn_1723_ = lean_ctor_get(v_v_1694_, 28);
v_negFn_1724_ = lean_ctor_get(v_v_1694_, 29);
v_vars_1725_ = lean_ctor_get(v_v_1694_, 30);
v_varMap_1726_ = lean_ctor_get(v_v_1694_, 31);
v_lowers_1727_ = lean_ctor_get(v_v_1694_, 32);
v_uppers_1728_ = lean_ctor_get(v_v_1694_, 33);
v_diseqs_1729_ = lean_ctor_get(v_v_1694_, 34);
v_assignment_1730_ = lean_ctor_get(v_v_1694_, 35);
v_caseSplits_1731_ = lean_ctor_get_uint8(v_v_1694_, sizeof(void*)*42);
v_conflict_x3f_1732_ = lean_ctor_get(v_v_1694_, 36);
v_diseqSplits_1733_ = lean_ctor_get(v_v_1694_, 37);
v_elimEqs_1734_ = lean_ctor_get(v_v_1694_, 38);
v_elimStack_1735_ = lean_ctor_get(v_v_1694_, 39);
v_occurs_1736_ = lean_ctor_get(v_v_1694_, 40);
v_ignored_1737_ = lean_ctor_get(v_v_1694_, 41);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_v_1694_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1739_ = v_v_1694_;
v_isShared_1740_ = v_isSharedCheck_1751_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_ignored_1737_);
lean_inc(v_occurs_1736_);
lean_inc(v_elimStack_1735_);
lean_inc(v_elimEqs_1734_);
lean_inc(v_diseqSplits_1733_);
lean_inc(v_conflict_x3f_1732_);
lean_inc(v_assignment_1730_);
lean_inc(v_diseqs_1729_);
lean_inc(v_uppers_1728_);
lean_inc(v_lowers_1727_);
lean_inc(v_varMap_1726_);
lean_inc(v_vars_1725_);
lean_inc(v_negFn_1724_);
lean_inc(v_subFn_1723_);
lean_inc(v_homomulFn_x3f_1722_);
lean_inc(v_nsmulFn_x3f_1721_);
lean_inc(v_zsmulFn_x3f_1720_);
lean_inc(v_nsmulFn_1719_);
lean_inc(v_zsmulFn_1718_);
lean_inc(v_addFn_1717_);
lean_inc(v_ltFn_x3f_1716_);
lean_inc(v_leFn_x3f_1715_);
lean_inc(v_one_x3f_1714_);
lean_inc(v_ofNatZero_1713_);
lean_inc(v_zero_1712_);
lean_inc(v_charInst_x3f_1711_);
lean_inc(v_fieldInst_x3f_1710_);
lean_inc(v_orderedRingInst_x3f_1709_);
lean_inc(v_commRingInst_x3f_1708_);
lean_inc(v_ringInst_x3f_1707_);
lean_inc(v_noNatDivInst_x3f_1706_);
lean_inc(v_isLinearInst_x3f_1705_);
lean_inc(v_orderedAddInst_x3f_1704_);
lean_inc(v_isPreorderInst_x3f_1703_);
lean_inc(v_lawfulOrderLTInst_x3f_1702_);
lean_inc(v_ltInst_x3f_1701_);
lean_inc(v_leInst_x3f_1700_);
lean_inc(v_intModuleInst_1699_);
lean_inc(v_u_1698_);
lean_inc(v_type_1697_);
lean_inc(v_ringId_x3f_1696_);
lean_inc(v_id_1695_);
lean_dec(v_v_1694_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1751_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v_xs_x27_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1741_ = lean_box(0);
v_xs_x27_1742_ = lean_array_fset(v_structs_1681_, v_a_1678_, v___x_1741_);
v___x_1743_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1730_, v_x_1679_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 35, v___x_1743_);
v___x_1745_ = v___x_1739_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_id_1695_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_ringId_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_type_1697_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_u_1698_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_intModuleInst_1699_);
lean_ctor_set(v_reuseFailAlloc_1750_, 5, v_leInst_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1750_, 6, v_ltInst_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1750_, 7, v_lawfulOrderLTInst_x3f_1702_);
lean_ctor_set(v_reuseFailAlloc_1750_, 8, v_isPreorderInst_x3f_1703_);
lean_ctor_set(v_reuseFailAlloc_1750_, 9, v_orderedAddInst_x3f_1704_);
lean_ctor_set(v_reuseFailAlloc_1750_, 10, v_isLinearInst_x3f_1705_);
lean_ctor_set(v_reuseFailAlloc_1750_, 11, v_noNatDivInst_x3f_1706_);
lean_ctor_set(v_reuseFailAlloc_1750_, 12, v_ringInst_x3f_1707_);
lean_ctor_set(v_reuseFailAlloc_1750_, 13, v_commRingInst_x3f_1708_);
lean_ctor_set(v_reuseFailAlloc_1750_, 14, v_orderedRingInst_x3f_1709_);
lean_ctor_set(v_reuseFailAlloc_1750_, 15, v_fieldInst_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1750_, 16, v_charInst_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1750_, 17, v_zero_1712_);
lean_ctor_set(v_reuseFailAlloc_1750_, 18, v_ofNatZero_1713_);
lean_ctor_set(v_reuseFailAlloc_1750_, 19, v_one_x3f_1714_);
lean_ctor_set(v_reuseFailAlloc_1750_, 20, v_leFn_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1750_, 21, v_ltFn_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1750_, 22, v_addFn_1717_);
lean_ctor_set(v_reuseFailAlloc_1750_, 23, v_zsmulFn_1718_);
lean_ctor_set(v_reuseFailAlloc_1750_, 24, v_nsmulFn_1719_);
lean_ctor_set(v_reuseFailAlloc_1750_, 25, v_zsmulFn_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1750_, 26, v_nsmulFn_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1750_, 27, v_homomulFn_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1750_, 28, v_subFn_1723_);
lean_ctor_set(v_reuseFailAlloc_1750_, 29, v_negFn_1724_);
lean_ctor_set(v_reuseFailAlloc_1750_, 30, v_vars_1725_);
lean_ctor_set(v_reuseFailAlloc_1750_, 31, v_varMap_1726_);
lean_ctor_set(v_reuseFailAlloc_1750_, 32, v_lowers_1727_);
lean_ctor_set(v_reuseFailAlloc_1750_, 33, v_uppers_1728_);
lean_ctor_set(v_reuseFailAlloc_1750_, 34, v_diseqs_1729_);
lean_ctor_set(v_reuseFailAlloc_1750_, 35, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1750_, 36, v_conflict_x3f_1732_);
lean_ctor_set(v_reuseFailAlloc_1750_, 37, v_diseqSplits_1733_);
lean_ctor_set(v_reuseFailAlloc_1750_, 38, v_elimEqs_1734_);
lean_ctor_set(v_reuseFailAlloc_1750_, 39, v_elimStack_1735_);
lean_ctor_set(v_reuseFailAlloc_1750_, 40, v_occurs_1736_);
lean_ctor_set(v_reuseFailAlloc_1750_, 41, v_ignored_1737_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*42, v_caseSplits_1731_);
v___x_1745_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_array_fset(v_xs_x27_1742_, v_a_1678_, v___x_1745_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1746_);
v___x_1748_ = v___x_1692_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_typeIdOf_1682_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_exprToStructId_1683_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_exprToStructIdEntries_1684_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_forbiddenNatModules_1685_);
lean_ctor_set(v_reuseFailAlloc_1749_, 5, v_natStructs_1686_);
lean_ctor_set(v_reuseFailAlloc_1749_, 6, v_natTypeIdOf_1687_);
lean_ctor_set(v_reuseFailAlloc_1749_, 7, v_exprToNatStructId_1688_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1761_, lean_object* v_x_1762_, lean_object* v_s_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1761_, v_x_1762_, v_s_1763_);
lean_dec(v_x_1762_);
lean_dec(v_a_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_inc(v_a_1766_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1769_, 0, v_a_1766_);
lean_closure_set(v___f_1769_, 1, v_x_1765_);
v___x_1770_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1770_, v___f_1769_, v_a_1767_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec(v_a_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1777_, v_a_1778_, v_a_1779_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec(v_a_1792_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = l_Lean_instInhabitedExpr;
v___x_1819_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1835_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1835_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_vars_1824_; lean_object* v_size_1825_; uint8_t v___x_1826_; 
v_vars_1824_ = lean_ctor_get(v_a_1820_, 30);
lean_inc_ref(v_vars_1824_);
lean_dec(v_a_1820_);
v_size_1825_ = lean_ctor_get(v_vars_1824_, 2);
v___x_1826_ = lean_nat_dec_lt(v_x_1805_, v_size_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec_ref(v_vars_1824_);
v___x_1827_ = l_outOfBounds___redArg(v___x_1818_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1827_);
v___x_1829_ = v___x_1822_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1818_, v_vars_1824_, v_x_1805_);
lean_dec_ref(v_vars_1824_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1831_);
v___x_1833_ = v___x_1822_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1819_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1819_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec(v_x_1844_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1859_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; uint8_t v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v___x_1872_ = lean_unbox(v_a_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1873_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1887_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_conflict_x3f_1878_; 
v_conflict_x3f_1878_ = lean_ctor_get(v_a_1874_, 36);
lean_inc(v_conflict_x3f_1878_);
lean_dec(v_a_1874_);
if (lean_obj_tag(v_conflict_x3f_1878_) == 0)
{
lean_object* v___x_1880_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_a_1871_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1871_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
else
{
uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec_ref_known(v_conflict_x3f_1878_, 1);
lean_dec(v_a_1871_);
v___x_1882_ = 1;
v___x_1883_ = lean_box(v___x_1882_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1883_);
v___x_1885_ = v___x_1876_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_a_1871_);
v_a_1888_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1873_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1873_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
return v___x_1870_;
}
}
else
{
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_box(0);
v___x_1923_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1945_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1945_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___y_1929_; lean_object* v_elimEqs_1940_; lean_object* v_size_1941_; uint8_t v___x_1942_; 
v_elimEqs_1940_ = lean_ctor_get(v_a_1924_, 38);
lean_inc_ref(v_elimEqs_1940_);
lean_dec(v_a_1924_);
v_size_1941_ = lean_ctor_get(v_elimEqs_1940_, 2);
v___x_1942_ = lean_nat_dec_lt(v_x_1909_, v_size_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; 
lean_dec_ref(v_elimEqs_1940_);
v___x_1943_ = l_outOfBounds___redArg(v___x_1922_);
v___y_1929_ = v___x_1943_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1922_, v_elimEqs_1940_, v_x_1909_);
lean_dec_ref(v_elimEqs_1940_);
v___y_1929_ = v___x_1944_;
goto v___jp_1928_;
}
v___jp_1928_:
{
if (lean_obj_tag(v___y_1929_) == 0)
{
uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = 0;
v___x_1931_ = lean_box(v___x_1930_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1931_);
v___x_1933_ = v___x_1926_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
else
{
uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_dec_ref_known(v___y_1929_, 1);
v___x_1935_ = 1;
v___x_1936_ = lean_box(v___x_1935_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1936_);
v___x_1938_ = v___x_1926_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1923_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1923_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec(v_x_1954_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1998_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1998_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1998_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_occurs_1986_; lean_object* v_size_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_occurs_1986_ = lean_ctor_get(v_a_1982_, 40);
lean_inc_ref(v_occurs_1986_);
lean_dec(v_a_1982_);
v_size_1987_ = lean_ctor_get(v_occurs_1986_, 2);
v___x_1988_ = lean_box(1);
v___x_1989_ = lean_nat_dec_lt(v_x_1968_, v_size_1987_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec_ref(v_occurs_1986_);
v___x_1990_ = l_outOfBounds___redArg(v___x_1988_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1988_, v_occurs_1986_, v_x_1968_);
lean_dec_ref(v_occurs_1986_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1994_);
v___x_1996_ = v___x_1984_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_a_1999_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1981_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1981_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec(v_x_2007_);
return v_res_2020_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_2021_, lean_object* v_t_2022_){
_start:
{
if (lean_obj_tag(v_t_2022_) == 0)
{
lean_object* v_k_2023_; lean_object* v_l_2024_; lean_object* v_r_2025_; uint8_t v___x_2026_; 
v_k_2023_ = lean_ctor_get(v_t_2022_, 1);
v_l_2024_ = lean_ctor_get(v_t_2022_, 3);
v_r_2025_ = lean_ctor_get(v_t_2022_, 4);
v___x_2026_ = lean_nat_dec_lt(v_k_2021_, v_k_2023_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_nat_dec_eq(v_k_2021_, v_k_2023_);
if (v___x_2027_ == 0)
{
v_t_2022_ = v_r_2025_;
goto _start;
}
else
{
return v___x_2027_;
}
}
else
{
v_t_2022_ = v_l_2024_;
goto _start;
}
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_2031_, lean_object* v_t_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2031_, v_t_2032_);
lean_dec(v_t_2032_);
lean_dec(v_k_2031_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_2035_, lean_object* v_v_2036_, lean_object* v_t_2037_){
_start:
{
if (lean_obj_tag(v_t_2037_) == 0)
{
lean_object* v_size_2038_; lean_object* v_k_2039_; lean_object* v_v_2040_; lean_object* v_l_2041_; lean_object* v_r_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2323_; 
v_size_2038_ = lean_ctor_get(v_t_2037_, 0);
v_k_2039_ = lean_ctor_get(v_t_2037_, 1);
v_v_2040_ = lean_ctor_get(v_t_2037_, 2);
v_l_2041_ = lean_ctor_get(v_t_2037_, 3);
v_r_2042_ = lean_ctor_get(v_t_2037_, 4);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_t_2037_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2044_ = v_t_2037_;
v_isShared_2045_ = v_isSharedCheck_2323_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_r_2042_);
lean_inc(v_l_2041_);
lean_inc(v_v_2040_);
lean_inc(v_k_2039_);
lean_inc(v_size_2038_);
lean_dec(v_t_2037_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2323_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_lt(v_k_2035_, v_k_2039_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_nat_dec_eq(v_k_2035_, v_k_2039_);
if (v___x_2047_ == 0)
{
lean_object* v_impl_2048_; lean_object* v___x_2049_; 
lean_dec(v_size_2038_);
v_impl_2048_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2035_, v_v_2036_, v_r_2042_);
v___x_2049_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2041_) == 0)
{
lean_object* v_size_2050_; lean_object* v_size_2051_; lean_object* v_k_2052_; lean_object* v_v_2053_; lean_object* v_l_2054_; lean_object* v_r_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_size_2050_ = lean_ctor_get(v_l_2041_, 0);
v_size_2051_ = lean_ctor_get(v_impl_2048_, 0);
v_k_2052_ = lean_ctor_get(v_impl_2048_, 1);
v_v_2053_ = lean_ctor_get(v_impl_2048_, 2);
v_l_2054_ = lean_ctor_get(v_impl_2048_, 3);
lean_inc(v_l_2054_);
v_r_2055_ = lean_ctor_get(v_impl_2048_, 4);
v___x_2056_ = lean_unsigned_to_nat(3u);
v___x_2057_ = lean_nat_mul(v___x_2056_, v_size_2050_);
v___x_2058_ = lean_nat_dec_lt(v___x_2057_, v_size_2051_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v_l_2054_);
v___x_2059_ = lean_nat_add(v___x_2049_, v_size_2050_);
v___x_2060_ = lean_nat_add(v___x_2059_, v_size_2051_);
lean_dec(v___x_2059_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_impl_2048_);
lean_ctor_set(v___x_2044_, 0, v___x_2060_);
v___x_2062_ = v___x_2044_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_impl_2048_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2127_; 
lean_inc(v_r_2055_);
lean_inc(v_v_2053_);
lean_inc(v_k_2052_);
lean_inc(v_size_2051_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_impl_2048_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2128_ = lean_ctor_get(v_impl_2048_, 4);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_impl_2048_, 3);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_impl_2048_, 2);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_impl_2048_, 1);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_impl_2048_, 0);
lean_dec(v_unused_2132_);
v___x_2065_ = v_impl_2048_;
v_isShared_2066_ = v_isSharedCheck_2127_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v_impl_2048_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2127_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_size_2067_; lean_object* v_k_2068_; lean_object* v_v_2069_; lean_object* v_l_2070_; lean_object* v_r_2071_; lean_object* v_size_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_size_2067_ = lean_ctor_get(v_l_2054_, 0);
v_k_2068_ = lean_ctor_get(v_l_2054_, 1);
v_v_2069_ = lean_ctor_get(v_l_2054_, 2);
v_l_2070_ = lean_ctor_get(v_l_2054_, 3);
v_r_2071_ = lean_ctor_get(v_l_2054_, 4);
v_size_2072_ = lean_ctor_get(v_r_2055_, 0);
v___x_2073_ = lean_unsigned_to_nat(2u);
v___x_2074_ = lean_nat_mul(v___x_2073_, v_size_2072_);
v___x_2075_ = lean_nat_dec_lt(v_size_2067_, v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2103_; 
lean_inc(v_r_2071_);
lean_inc(v_l_2070_);
lean_inc(v_v_2069_);
lean_inc(v_k_2068_);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_l_2054_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; lean_object* v_unused_2107_; lean_object* v_unused_2108_; 
v_unused_2104_ = lean_ctor_get(v_l_2054_, 4);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_l_2054_, 3);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_2054_, 2);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_l_2054_, 1);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_l_2054_, 0);
lean_dec(v_unused_2108_);
v___x_2077_ = v_l_2054_;
v_isShared_2078_ = v_isSharedCheck_2103_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v_l_2054_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2103_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2093_; 
v___x_2079_ = lean_nat_add(v___x_2049_, v_size_2050_);
v___x_2080_ = lean_nat_add(v___x_2079_, v_size_2051_);
lean_dec(v_size_2051_);
if (lean_obj_tag(v_l_2070_) == 0)
{
lean_object* v_size_2101_; 
v_size_2101_ = lean_ctor_get(v_l_2070_, 0);
lean_inc(v_size_2101_);
v___y_2093_ = v_size_2101_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_unsigned_to_nat(0u);
v___y_2093_ = v___x_2102_;
goto v___jp_2092_;
}
v___jp_2081_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_nat_add(v___y_2082_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec(v___y_2082_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 4, v_r_2055_);
lean_ctor_set(v___x_2077_, 3, v_r_2071_);
lean_ctor_set(v___x_2077_, 2, v_v_2053_);
lean_ctor_set(v___x_2077_, 1, v_k_2052_);
lean_ctor_set(v___x_2077_, 0, v___x_2085_);
v___x_2087_ = v___x_2077_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_2052_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_2053_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_r_2071_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_r_2055_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 4, v___x_2087_);
lean_ctor_set(v___x_2065_, 3, v___y_2083_);
lean_ctor_set(v___x_2065_, 2, v_v_2069_);
lean_ctor_set(v___x_2065_, 1, v_k_2068_);
lean_ctor_set(v___x_2065_, 0, v___x_2080_);
v___x_2089_ = v___x_2065_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_2068_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v___y_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
v___jp_2092_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_nat_add(v___x_2079_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec(v___x_2079_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_l_2070_);
lean_ctor_set(v___x_2044_, 0, v___x_2094_);
v___x_2096_ = v___x_2044_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_l_2070_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_nat_add(v___x_2049_, v_size_2072_);
if (lean_obj_tag(v_r_2071_) == 0)
{
lean_object* v_size_2098_; 
v_size_2098_ = lean_ctor_get(v_r_2071_, 0);
lean_inc(v_size_2098_);
v___y_2082_ = v___x_2097_;
v___y_2083_ = v___x_2096_;
v___y_2084_ = v_size_2098_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_unsigned_to_nat(0u);
v___y_2082_ = v___x_2097_;
v___y_2083_ = v___x_2096_;
v___y_2084_ = v___x_2099_;
goto v___jp_2081_;
}
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_del_object(v___x_2044_);
v___x_2109_ = lean_nat_add(v___x_2049_, v_size_2050_);
v___x_2110_ = lean_nat_add(v___x_2109_, v_size_2051_);
lean_dec(v_size_2051_);
v___x_2111_ = lean_nat_add(v___x_2109_, v_size_2067_);
lean_dec(v___x_2109_);
lean_inc_ref(v_l_2041_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 4, v_l_2054_);
lean_ctor_set(v___x_2065_, 3, v_l_2041_);
lean_ctor_set(v___x_2065_, 2, v_v_2040_);
lean_ctor_set(v___x_2065_, 1, v_k_2039_);
lean_ctor_set(v___x_2065_, 0, v___x_2111_);
v___x_2113_ = v___x_2065_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_l_2054_);
v___x_2113_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v_l_2041_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; lean_object* v_unused_2125_; 
v_unused_2121_ = lean_ctor_get(v_l_2041_, 4);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_l_2041_, 3);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_l_2041_, 2);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_l_2041_, 1);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_l_2041_, 0);
lean_dec(v_unused_2125_);
v___x_2115_ = v_l_2041_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v_l_2041_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 4, v_r_2055_);
lean_ctor_set(v___x_2115_, 3, v___x_2113_);
lean_ctor_set(v___x_2115_, 2, v_v_2053_);
lean_ctor_set(v___x_2115_, 1, v_k_2052_);
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_k_2052_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_v_2053_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_r_2055_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2133_; 
v_l_2133_ = lean_ctor_get(v_impl_2048_, 3);
lean_inc(v_l_2133_);
if (lean_obj_tag(v_l_2133_) == 0)
{
lean_object* v_r_2134_; lean_object* v_k_2135_; lean_object* v_v_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2159_; 
v_r_2134_ = lean_ctor_get(v_impl_2048_, 4);
v_k_2135_ = lean_ctor_get(v_impl_2048_, 1);
v_v_2136_ = lean_ctor_get(v_impl_2048_, 2);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_impl_2048_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2160_ = lean_ctor_get(v_impl_2048_, 3);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_impl_2048_, 0);
lean_dec(v_unused_2161_);
v___x_2138_ = v_impl_2048_;
v_isShared_2139_ = v_isSharedCheck_2159_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_r_2134_);
lean_inc(v_v_2136_);
lean_inc(v_k_2135_);
lean_dec(v_impl_2048_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2159_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_k_2140_; lean_object* v_v_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2155_; 
v_k_2140_ = lean_ctor_get(v_l_2133_, 1);
v_v_2141_ = lean_ctor_get(v_l_2133_, 2);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_l_2133_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2156_ = lean_ctor_get(v_l_2133_, 4);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_2133_, 3);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_l_2133_, 0);
lean_dec(v_unused_2158_);
v___x_2143_ = v_l_2133_;
v_isShared_2144_ = v_isSharedCheck_2155_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_v_2141_);
lean_inc(v_k_2140_);
lean_dec(v_l_2133_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2155_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2134_, 2);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v_r_2134_);
lean_ctor_set(v___x_2143_, 3, v_r_2134_);
lean_ctor_set(v___x_2143_, 2, v_v_2040_);
lean_ctor_set(v___x_2143_, 1, v_k_2039_);
lean_ctor_set(v___x_2143_, 0, v___x_2049_);
v___x_2147_ = v___x_2143_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_r_2134_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_r_2134_);
v___x_2147_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
lean_inc(v_r_2134_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 3, v_r_2134_);
lean_ctor_set(v___x_2138_, 0, v___x_2049_);
v___x_2149_ = v___x_2138_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_r_2134_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_r_2134_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v___x_2149_);
lean_ctor_set(v___x_2044_, 3, v___x_2147_);
lean_ctor_set(v___x_2044_, 2, v_v_2141_);
lean_ctor_set(v___x_2044_, 1, v_k_2140_);
lean_ctor_set(v___x_2044_, 0, v___x_2145_);
v___x_2151_ = v___x_2044_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2141_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_object* v_r_2162_; 
v_r_2162_ = lean_ctor_get(v_impl_2048_, 4);
lean_inc(v_r_2162_);
if (lean_obj_tag(v_r_2162_) == 0)
{
lean_object* v_k_2163_; lean_object* v_v_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2175_; 
v_k_2163_ = lean_ctor_get(v_impl_2048_, 1);
v_v_2164_ = lean_ctor_get(v_impl_2048_, 2);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_impl_2048_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; 
v_unused_2176_ = lean_ctor_get(v_impl_2048_, 4);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_impl_2048_, 3);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_impl_2048_, 0);
lean_dec(v_unused_2178_);
v___x_2166_ = v_impl_2048_;
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_v_2164_);
lean_inc(v_k_2163_);
lean_dec(v_impl_2048_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_unsigned_to_nat(3u);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 4, v_l_2133_);
lean_ctor_set(v___x_2166_, 2, v_v_2040_);
lean_ctor_set(v___x_2166_, 1, v_k_2039_);
lean_ctor_set(v___x_2166_, 0, v___x_2049_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_l_2133_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_l_2133_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_r_2162_);
lean_ctor_set(v___x_2044_, 3, v___x_2170_);
lean_ctor_set(v___x_2044_, 2, v_v_2164_);
lean_ctor_set(v___x_2044_, 1, v_k_2163_);
lean_ctor_set(v___x_2044_, 0, v___x_2168_);
v___x_2172_ = v___x_2044_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_2163_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_2164_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_r_2162_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(2u);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_impl_2048_);
lean_ctor_set(v___x_2044_, 3, v_r_2162_);
lean_ctor_set(v___x_2044_, 0, v___x_2179_);
v___x_2181_ = v___x_2044_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_r_2162_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_impl_2048_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v___x_2184_; 
lean_dec(v_v_2040_);
lean_dec(v_k_2039_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 2, v_v_2036_);
lean_ctor_set(v___x_2044_, 1, v_k_2035_);
v___x_2184_ = v___x_2044_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_size_2038_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2035_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_v_2036_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_r_2042_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v_impl_2186_; lean_object* v___x_2187_; 
lean_dec(v_size_2038_);
v_impl_2186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2035_, v_v_2036_, v_l_2041_);
v___x_2187_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2042_) == 0)
{
lean_object* v_size_2188_; lean_object* v_size_2189_; lean_object* v_k_2190_; lean_object* v_v_2191_; lean_object* v_l_2192_; lean_object* v_r_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_size_2188_ = lean_ctor_get(v_r_2042_, 0);
v_size_2189_ = lean_ctor_get(v_impl_2186_, 0);
v_k_2190_ = lean_ctor_get(v_impl_2186_, 1);
v_v_2191_ = lean_ctor_get(v_impl_2186_, 2);
v_l_2192_ = lean_ctor_get(v_impl_2186_, 3);
v_r_2193_ = lean_ctor_get(v_impl_2186_, 4);
lean_inc(v_r_2193_);
v___x_2194_ = lean_unsigned_to_nat(3u);
v___x_2195_ = lean_nat_mul(v___x_2194_, v_size_2188_);
v___x_2196_ = lean_nat_dec_lt(v___x_2195_, v_size_2189_);
lean_dec(v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_dec(v_r_2193_);
v___x_2197_ = lean_nat_add(v___x_2187_, v_size_2189_);
v___x_2198_ = lean_nat_add(v___x_2197_, v_size_2188_);
lean_dec(v___x_2197_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 3, v_impl_2186_);
lean_ctor_set(v___x_2044_, 0, v___x_2198_);
v___x_2200_ = v___x_2044_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_impl_2186_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_2042_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2267_; 
lean_inc(v_l_2192_);
lean_inc(v_v_2191_);
lean_inc(v_k_2190_);
lean_inc(v_size_2189_);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_impl_2186_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; lean_object* v_unused_2272_; 
v_unused_2268_ = lean_ctor_get(v_impl_2186_, 4);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_impl_2186_, 3);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_impl_2186_, 2);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_impl_2186_, 1);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_impl_2186_, 0);
lean_dec(v_unused_2272_);
v___x_2203_ = v_impl_2186_;
v_isShared_2204_ = v_isSharedCheck_2267_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v_impl_2186_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2267_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_size_2205_; lean_object* v_size_2206_; lean_object* v_k_2207_; lean_object* v_v_2208_; lean_object* v_l_2209_; lean_object* v_r_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_size_2205_ = lean_ctor_get(v_l_2192_, 0);
v_size_2206_ = lean_ctor_get(v_r_2193_, 0);
v_k_2207_ = lean_ctor_get(v_r_2193_, 1);
v_v_2208_ = lean_ctor_get(v_r_2193_, 2);
v_l_2209_ = lean_ctor_get(v_r_2193_, 3);
v_r_2210_ = lean_ctor_get(v_r_2193_, 4);
v___x_2211_ = lean_unsigned_to_nat(2u);
v___x_2212_ = lean_nat_mul(v___x_2211_, v_size_2205_);
v___x_2213_ = lean_nat_dec_lt(v_size_2206_, v___x_2212_);
lean_dec(v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2242_; 
lean_inc(v_r_2210_);
lean_inc(v_l_2209_);
lean_inc(v_v_2208_);
lean_inc(v_k_2207_);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_r_2193_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; lean_object* v_unused_2245_; lean_object* v_unused_2246_; lean_object* v_unused_2247_; 
v_unused_2243_ = lean_ctor_get(v_r_2193_, 4);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_r_2193_, 3);
lean_dec(v_unused_2244_);
v_unused_2245_ = lean_ctor_get(v_r_2193_, 2);
lean_dec(v_unused_2245_);
v_unused_2246_ = lean_ctor_get(v_r_2193_, 1);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_r_2193_, 0);
lean_dec(v_unused_2247_);
v___x_2215_ = v_r_2193_;
v_isShared_2216_ = v_isSharedCheck_2242_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v_r_2193_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2242_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___x_2230_; lean_object* v___y_2232_; 
v___x_2217_ = lean_nat_add(v___x_2187_, v_size_2189_);
lean_dec(v_size_2189_);
v___x_2218_ = lean_nat_add(v___x_2217_, v_size_2188_);
lean_dec(v___x_2217_);
v___x_2230_ = lean_nat_add(v___x_2187_, v_size_2205_);
if (lean_obj_tag(v_l_2209_) == 0)
{
lean_object* v_size_2240_; 
v_size_2240_ = lean_ctor_get(v_l_2209_, 0);
lean_inc(v_size_2240_);
v___y_2232_ = v_size_2240_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___y_2232_ = v___x_2241_;
goto v___jp_2231_;
}
v___jp_2219_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_nat_add(v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec(v___y_2221_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 4, v_r_2042_);
lean_ctor_set(v___x_2215_, 3, v_r_2210_);
lean_ctor_set(v___x_2215_, 2, v_v_2040_);
lean_ctor_set(v___x_2215_, 1, v_k_2039_);
lean_ctor_set(v___x_2215_, 0, v___x_2223_);
v___x_2225_ = v___x_2215_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_r_2210_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_r_2042_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v___x_2225_);
lean_ctor_set(v___x_2203_, 3, v___y_2220_);
lean_ctor_set(v___x_2203_, 2, v_v_2208_);
lean_ctor_set(v___x_2203_, 1, v_k_2207_);
lean_ctor_set(v___x_2203_, 0, v___x_2218_);
v___x_2227_ = v___x_2203_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2207_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2208_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v___y_2220_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_nat_add(v___x_2230_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec(v___x_2230_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_l_2209_);
lean_ctor_set(v___x_2044_, 3, v_l_2192_);
lean_ctor_set(v___x_2044_, 2, v_v_2191_);
lean_ctor_set(v___x_2044_, 1, v_k_2190_);
lean_ctor_set(v___x_2044_, 0, v___x_2233_);
v___x_2235_ = v___x_2044_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_l_2192_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_l_2209_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_nat_add(v___x_2187_, v_size_2188_);
if (lean_obj_tag(v_r_2210_) == 0)
{
lean_object* v_size_2237_; 
v_size_2237_ = lean_ctor_get(v_r_2210_, 0);
lean_inc(v_size_2237_);
v___y_2220_ = v___x_2235_;
v___y_2221_ = v___x_2236_;
v___y_2222_ = v_size_2237_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_unsigned_to_nat(0u);
v___y_2220_ = v___x_2235_;
v___y_2221_ = v___x_2236_;
v___y_2222_ = v___x_2238_;
goto v___jp_2219_;
}
}
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_del_object(v___x_2044_);
v___x_2248_ = lean_nat_add(v___x_2187_, v_size_2189_);
lean_dec(v_size_2189_);
v___x_2249_ = lean_nat_add(v___x_2248_, v_size_2188_);
lean_dec(v___x_2248_);
v___x_2250_ = lean_nat_add(v___x_2187_, v_size_2188_);
v___x_2251_ = lean_nat_add(v___x_2250_, v_size_2206_);
lean_dec(v___x_2250_);
lean_inc_ref(v_r_2042_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v_r_2042_);
lean_ctor_set(v___x_2203_, 3, v_r_2193_);
lean_ctor_set(v___x_2203_, 2, v_v_2040_);
lean_ctor_set(v___x_2203_, 1, v_k_2039_);
lean_ctor_set(v___x_2203_, 0, v___x_2251_);
v___x_2253_ = v___x_2203_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_r_2193_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_r_2042_);
v___x_2253_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_isSharedCheck_2260_ = !lean_is_exclusive(v_r_2042_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; lean_object* v_unused_2265_; 
v_unused_2261_ = lean_ctor_get(v_r_2042_, 4);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_r_2042_, 3);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_r_2042_, 2);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_r_2042_, 1);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_r_2042_, 0);
lean_dec(v_unused_2265_);
v___x_2255_ = v_r_2042_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_dec(v_r_2042_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 4, v___x_2253_);
lean_ctor_set(v___x_2255_, 3, v_l_2192_);
lean_ctor_set(v___x_2255_, 2, v_v_2191_);
lean_ctor_set(v___x_2255_, 1, v_k_2190_);
lean_ctor_set(v___x_2255_, 0, v___x_2249_);
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_k_2190_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_v_2191_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_l_2192_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v___x_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2273_; 
v_l_2273_ = lean_ctor_get(v_impl_2186_, 3);
if (lean_obj_tag(v_l_2273_) == 0)
{
lean_object* v_r_2274_; lean_object* v_k_2275_; lean_object* v_v_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2287_; 
lean_inc_ref(v_l_2273_);
v_r_2274_ = lean_ctor_get(v_impl_2186_, 4);
v_k_2275_ = lean_ctor_get(v_impl_2186_, 1);
v_v_2276_ = lean_ctor_get(v_impl_2186_, 2);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_impl_2186_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; 
v_unused_2288_ = lean_ctor_get(v_impl_2186_, 3);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_impl_2186_, 0);
lean_dec(v_unused_2289_);
v___x_2278_ = v_impl_2186_;
v_isShared_2279_ = v_isSharedCheck_2287_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_r_2274_);
lean_inc(v_v_2276_);
lean_inc(v_k_2275_);
lean_dec(v_impl_2186_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2287_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2274_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 3, v_r_2274_);
lean_ctor_set(v___x_2278_, 2, v_v_2040_);
lean_ctor_set(v___x_2278_, 1, v_k_2039_);
lean_ctor_set(v___x_2278_, 0, v___x_2187_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_r_2274_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_r_2274_);
v___x_2282_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v___x_2282_);
lean_ctor_set(v___x_2044_, 3, v_l_2273_);
lean_ctor_set(v___x_2044_, 2, v_v_2276_);
lean_ctor_set(v___x_2044_, 1, v_k_2275_);
lean_ctor_set(v___x_2044_, 0, v___x_2280_);
v___x_2284_ = v___x_2044_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2275_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2276_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_l_2273_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2282_);
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
lean_object* v_r_2290_; 
v_r_2290_ = lean_ctor_get(v_impl_2186_, 4);
lean_inc(v_r_2290_);
if (lean_obj_tag(v_r_2290_) == 0)
{
lean_object* v_k_2291_; lean_object* v_v_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2315_; 
lean_inc(v_l_2273_);
v_k_2291_ = lean_ctor_get(v_impl_2186_, 1);
v_v_2292_ = lean_ctor_get(v_impl_2186_, 2);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_impl_2186_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; lean_object* v_unused_2317_; lean_object* v_unused_2318_; 
v_unused_2316_ = lean_ctor_get(v_impl_2186_, 4);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_impl_2186_, 3);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_impl_2186_, 0);
lean_dec(v_unused_2318_);
v___x_2294_ = v_impl_2186_;
v_isShared_2295_ = v_isSharedCheck_2315_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_v_2292_);
lean_inc(v_k_2291_);
lean_dec(v_impl_2186_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2315_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_k_2296_; lean_object* v_v_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2311_; 
v_k_2296_ = lean_ctor_get(v_r_2290_, 1);
v_v_2297_ = lean_ctor_get(v_r_2290_, 2);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_r_2290_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2312_ = lean_ctor_get(v_r_2290_, 4);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_r_2290_, 3);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_2290_, 0);
lean_dec(v_unused_2314_);
v___x_2299_ = v_r_2290_;
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_v_2297_);
lean_inc(v_k_2296_);
lean_dec(v_r_2290_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_unsigned_to_nat(3u);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 4, v_l_2273_);
lean_ctor_set(v___x_2299_, 3, v_l_2273_);
lean_ctor_set(v___x_2299_, 2, v_v_2292_);
lean_ctor_set(v___x_2299_, 1, v_k_2291_);
lean_ctor_set(v___x_2299_, 0, v___x_2187_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_2291_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_v_2292_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_l_2273_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_l_2273_);
v___x_2303_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 4, v_l_2273_);
lean_ctor_set(v___x_2294_, 2, v_v_2040_);
lean_ctor_set(v___x_2294_, 1, v_k_2039_);
lean_ctor_set(v___x_2294_, 0, v___x_2187_);
v___x_2305_ = v___x_2294_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_l_2273_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_l_2273_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v___x_2305_);
lean_ctor_set(v___x_2044_, 3, v___x_2303_);
lean_ctor_set(v___x_2044_, 2, v_v_2297_);
lean_ctor_set(v___x_2044_, 1, v_k_2296_);
lean_ctor_set(v___x_2044_, 0, v___x_2301_);
v___x_2307_ = v___x_2044_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_unsigned_to_nat(2u);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v_r_2290_);
lean_ctor_set(v___x_2044_, 3, v_impl_2186_);
lean_ctor_set(v___x_2044_, 0, v___x_2319_);
v___x_2321_ = v___x_2044_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_k_2039_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_v_2040_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_impl_2186_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_r_2290_);
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
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v_k_2035_);
lean_ctor_set(v___x_2325_, 2, v_v_2036_);
lean_ctor_set(v___x_2325_, 3, v_t_2037_);
lean_ctor_set(v___x_2325_, 4, v_t_2037_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2326_, lean_object* v_x_2327_, size_t v_x_2328_, size_t v_x_2329_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 0)
{
lean_object* v_cs_2330_; size_t v_j_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_cs_2330_ = lean_ctor_get(v_x_2327_, 0);
v_j_2331_ = lean_usize_shift_right(v_x_2328_, v_x_2329_);
v___x_2332_ = lean_usize_to_nat(v_j_2331_);
v___x_2333_ = lean_array_get_size(v_cs_2330_);
v___x_2334_ = lean_nat_dec_lt(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec(v___x_2332_);
lean_dec(v_y_2326_);
return v_x_2327_;
}
else
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2352_; 
lean_inc_ref(v_cs_2330_);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_x_2327_, 0);
lean_dec(v_unused_2353_);
v___x_2336_ = v_x_2327_;
v_isShared_2337_ = v_isSharedCheck_2352_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v_x_2327_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2352_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
size_t v___x_2338_; size_t v___x_2339_; size_t v___x_2340_; size_t v_i_2341_; size_t v___x_2342_; size_t v_shift_2343_; lean_object* v_v_2344_; lean_object* v___x_2345_; lean_object* v_xs_x27_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_shift_left(v___x_2338_, v_x_2329_);
v___x_2340_ = lean_usize_sub(v___x_2339_, v___x_2338_);
v_i_2341_ = lean_usize_land(v_x_2328_, v___x_2340_);
v___x_2342_ = ((size_t)5ULL);
v_shift_2343_ = lean_usize_sub(v_x_2329_, v___x_2342_);
v_v_2344_ = lean_array_fget(v_cs_2330_, v___x_2332_);
v___x_2345_ = lean_box(0);
v_xs_x27_2346_ = lean_array_fset(v_cs_2330_, v___x_2332_, v___x_2345_);
v___x_2347_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2326_, v_v_2344_, v_i_2341_, v_shift_2343_);
v___x_2348_ = lean_array_fset(v_xs_x27_2346_, v___x_2332_, v___x_2347_);
lean_dec(v___x_2332_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2348_);
v___x_2350_ = v___x_2336_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_vs_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_vs_2354_ = lean_ctor_get(v_x_2327_, 0);
v___x_2355_ = lean_usize_to_nat(v_x_2328_);
v___x_2356_ = lean_array_get_size(v_vs_2354_);
v___x_2357_ = lean_nat_dec_lt(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec(v___x_2355_);
lean_dec(v_y_2326_);
return v_x_2327_;
}
else
{
lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2372_; 
lean_inc_ref(v_vs_2354_);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v_x_2327_, 0);
lean_dec(v_unused_2373_);
v___x_2359_ = v_x_2327_;
v_isShared_2360_ = v_isSharedCheck_2372_;
goto v_resetjp_2358_;
}
else
{
lean_dec(v_x_2327_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2372_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_v_2361_; lean_object* v___x_2362_; lean_object* v_xs_x27_2363_; lean_object* v___y_2365_; uint8_t v___x_2370_; 
v_v_2361_ = lean_array_fget(v_vs_2354_, v___x_2355_);
v___x_2362_ = lean_box(0);
v_xs_x27_2363_ = lean_array_fset(v_vs_2354_, v___x_2355_, v___x_2362_);
v___x_2370_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2326_, v_v_2361_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2326_, v___x_2362_, v_v_2361_);
v___y_2365_ = v___x_2371_;
goto v___jp_2364_;
}
else
{
lean_dec(v_y_2326_);
v___y_2365_ = v_v_2361_;
goto v___jp_2364_;
}
v___jp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_array_fset(v_xs_x27_2363_, v___x_2355_, v___y_2365_);
lean_dec(v___x_2355_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2366_);
v___x_2368_ = v___x_2359_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
size_t v_x_5144__boxed_2378_; size_t v_x_5145__boxed_2379_; lean_object* v_res_2380_; 
v_x_5144__boxed_2378_ = lean_unbox_usize(v_x_2376_);
lean_dec(v_x_2376_);
v_x_5145__boxed_2379_ = lean_unbox_usize(v_x_2377_);
lean_dec(v_x_2377_);
v_res_2380_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2374_, v_x_2375_, v_x_5144__boxed_2378_, v_x_5145__boxed_2379_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2381_, lean_object* v_t_2382_, lean_object* v_i_2383_){
_start:
{
lean_object* v_root_2384_; lean_object* v_tail_2385_; lean_object* v_size_2386_; size_t v_shift_2387_; lean_object* v_tailOff_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2415_; 
v_root_2384_ = lean_ctor_get(v_t_2382_, 0);
v_tail_2385_ = lean_ctor_get(v_t_2382_, 1);
v_size_2386_ = lean_ctor_get(v_t_2382_, 2);
v_shift_2387_ = lean_ctor_get_usize(v_t_2382_, 4);
v_tailOff_2388_ = lean_ctor_get(v_t_2382_, 3);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_t_2382_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2390_ = v_t_2382_;
v_isShared_2391_ = v_isSharedCheck_2415_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_tailOff_2388_);
lean_inc(v_size_2386_);
lean_inc(v_tail_2385_);
lean_inc(v_root_2384_);
lean_dec(v_t_2382_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2415_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_nat_dec_le(v_tailOff_2388_, v_i_2383_);
if (v___x_2392_ == 0)
{
size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2393_ = lean_usize_of_nat(v_i_2383_);
v___x_2394_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2381_, v_root_2384_, v___x_2393_, v_shift_2387_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2394_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_tail_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_size_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_tailOff_2388_);
lean_ctor_set_usize(v_reuseFailAlloc_2397_, 4, v_shift_2387_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = lean_nat_sub(v_i_2383_, v_tailOff_2388_);
v___x_2399_ = lean_array_get_size(v_tail_2385_);
v___x_2400_ = lean_nat_dec_lt(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2402_; 
lean_dec(v___x_2398_);
lean_dec(v_y_2381_);
if (v_isShared_2391_ == 0)
{
v___x_2402_ = v___x_2390_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_root_2384_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_tail_2385_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_size_2386_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_tailOff_2388_);
lean_ctor_set_usize(v_reuseFailAlloc_2403_, 4, v_shift_2387_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
else
{
lean_object* v_v_2404_; lean_object* v___x_2405_; lean_object* v_xs_x27_2406_; lean_object* v___y_2408_; uint8_t v___x_2413_; 
v_v_2404_ = lean_array_fget(v_tail_2385_, v___x_2398_);
v___x_2405_ = lean_box(0);
v_xs_x27_2406_ = lean_array_fset(v_tail_2385_, v___x_2398_, v___x_2405_);
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2381_, v_v_2404_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2381_, v___x_2405_, v_v_2404_);
v___y_2408_ = v___x_2414_;
goto v___jp_2407_;
}
else
{
lean_dec(v_y_2381_);
v___y_2408_ = v_v_2404_;
goto v___jp_2407_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_array_fset(v_xs_x27_2406_, v___x_2398_, v___y_2408_);
lean_dec(v___x_2398_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2409_);
v___x_2411_ = v___x_2390_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_root_2384_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_size_2386_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_tailOff_2388_);
lean_ctor_set_usize(v_reuseFailAlloc_2412_, 4, v_shift_2387_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2416_, lean_object* v_t_2417_, lean_object* v_i_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2416_, v_t_2417_, v_i_2418_);
lean_dec(v_i_2418_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2420_, lean_object* v_y_2421_, lean_object* v_x_2422_, lean_object* v_s_2423_){
_start:
{
lean_object* v_structs_2424_; lean_object* v_typeIdOf_2425_; lean_object* v_exprToStructId_2426_; lean_object* v_exprToStructIdEntries_2427_; lean_object* v_forbiddenNatModules_2428_; lean_object* v_natStructs_2429_; lean_object* v_natTypeIdOf_2430_; lean_object* v_exprToNatStructId_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_structs_2424_ = lean_ctor_get(v_s_2423_, 0);
v_typeIdOf_2425_ = lean_ctor_get(v_s_2423_, 1);
v_exprToStructId_2426_ = lean_ctor_get(v_s_2423_, 2);
v_exprToStructIdEntries_2427_ = lean_ctor_get(v_s_2423_, 3);
v_forbiddenNatModules_2428_ = lean_ctor_get(v_s_2423_, 4);
v_natStructs_2429_ = lean_ctor_get(v_s_2423_, 5);
v_natTypeIdOf_2430_ = lean_ctor_get(v_s_2423_, 6);
v_exprToNatStructId_2431_ = lean_ctor_get(v_s_2423_, 7);
v___x_2432_ = lean_array_get_size(v_structs_2424_);
v___x_2433_ = lean_nat_dec_lt(v_a_2420_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec(v_y_2421_);
return v_s_2423_;
}
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2495_; 
lean_inc_ref(v_exprToNatStructId_2431_);
lean_inc_ref(v_natTypeIdOf_2430_);
lean_inc_ref(v_natStructs_2429_);
lean_inc_ref(v_forbiddenNatModules_2428_);
lean_inc_ref(v_exprToStructIdEntries_2427_);
lean_inc_ref(v_exprToStructId_2426_);
lean_inc_ref(v_typeIdOf_2425_);
lean_inc_ref(v_structs_2424_);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_s_2423_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; lean_object* v_unused_2497_; lean_object* v_unused_2498_; lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; 
v_unused_2496_ = lean_ctor_get(v_s_2423_, 7);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_s_2423_, 6);
lean_dec(v_unused_2497_);
v_unused_2498_ = lean_ctor_get(v_s_2423_, 5);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_s_2423_, 4);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_s_2423_, 3);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_s_2423_, 2);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_s_2423_, 1);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_s_2423_, 0);
lean_dec(v_unused_2503_);
v___x_2435_ = v_s_2423_;
v_isShared_2436_ = v_isSharedCheck_2495_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_s_2423_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2495_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_v_2437_; lean_object* v_id_2438_; lean_object* v_ringId_x3f_2439_; lean_object* v_type_2440_; lean_object* v_u_2441_; lean_object* v_intModuleInst_2442_; lean_object* v_leInst_x3f_2443_; lean_object* v_ltInst_x3f_2444_; lean_object* v_lawfulOrderLTInst_x3f_2445_; lean_object* v_isPreorderInst_x3f_2446_; lean_object* v_orderedAddInst_x3f_2447_; lean_object* v_isLinearInst_x3f_2448_; lean_object* v_noNatDivInst_x3f_2449_; lean_object* v_ringInst_x3f_2450_; lean_object* v_commRingInst_x3f_2451_; lean_object* v_orderedRingInst_x3f_2452_; lean_object* v_fieldInst_x3f_2453_; lean_object* v_charInst_x3f_2454_; lean_object* v_zero_2455_; lean_object* v_ofNatZero_2456_; lean_object* v_one_x3f_2457_; lean_object* v_leFn_x3f_2458_; lean_object* v_ltFn_x3f_2459_; lean_object* v_addFn_2460_; lean_object* v_zsmulFn_2461_; lean_object* v_nsmulFn_2462_; lean_object* v_zsmulFn_x3f_2463_; lean_object* v_nsmulFn_x3f_2464_; lean_object* v_homomulFn_x3f_2465_; lean_object* v_subFn_2466_; lean_object* v_negFn_2467_; lean_object* v_vars_2468_; lean_object* v_varMap_2469_; lean_object* v_lowers_2470_; lean_object* v_uppers_2471_; lean_object* v_diseqs_2472_; lean_object* v_assignment_2473_; uint8_t v_caseSplits_2474_; lean_object* v_conflict_x3f_2475_; lean_object* v_diseqSplits_2476_; lean_object* v_elimEqs_2477_; lean_object* v_elimStack_2478_; lean_object* v_occurs_2479_; lean_object* v_ignored_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2494_; 
v_v_2437_ = lean_array_fget(v_structs_2424_, v_a_2420_);
v_id_2438_ = lean_ctor_get(v_v_2437_, 0);
v_ringId_x3f_2439_ = lean_ctor_get(v_v_2437_, 1);
v_type_2440_ = lean_ctor_get(v_v_2437_, 2);
v_u_2441_ = lean_ctor_get(v_v_2437_, 3);
v_intModuleInst_2442_ = lean_ctor_get(v_v_2437_, 4);
v_leInst_x3f_2443_ = lean_ctor_get(v_v_2437_, 5);
v_ltInst_x3f_2444_ = lean_ctor_get(v_v_2437_, 6);
v_lawfulOrderLTInst_x3f_2445_ = lean_ctor_get(v_v_2437_, 7);
v_isPreorderInst_x3f_2446_ = lean_ctor_get(v_v_2437_, 8);
v_orderedAddInst_x3f_2447_ = lean_ctor_get(v_v_2437_, 9);
v_isLinearInst_x3f_2448_ = lean_ctor_get(v_v_2437_, 10);
v_noNatDivInst_x3f_2449_ = lean_ctor_get(v_v_2437_, 11);
v_ringInst_x3f_2450_ = lean_ctor_get(v_v_2437_, 12);
v_commRingInst_x3f_2451_ = lean_ctor_get(v_v_2437_, 13);
v_orderedRingInst_x3f_2452_ = lean_ctor_get(v_v_2437_, 14);
v_fieldInst_x3f_2453_ = lean_ctor_get(v_v_2437_, 15);
v_charInst_x3f_2454_ = lean_ctor_get(v_v_2437_, 16);
v_zero_2455_ = lean_ctor_get(v_v_2437_, 17);
v_ofNatZero_2456_ = lean_ctor_get(v_v_2437_, 18);
v_one_x3f_2457_ = lean_ctor_get(v_v_2437_, 19);
v_leFn_x3f_2458_ = lean_ctor_get(v_v_2437_, 20);
v_ltFn_x3f_2459_ = lean_ctor_get(v_v_2437_, 21);
v_addFn_2460_ = lean_ctor_get(v_v_2437_, 22);
v_zsmulFn_2461_ = lean_ctor_get(v_v_2437_, 23);
v_nsmulFn_2462_ = lean_ctor_get(v_v_2437_, 24);
v_zsmulFn_x3f_2463_ = lean_ctor_get(v_v_2437_, 25);
v_nsmulFn_x3f_2464_ = lean_ctor_get(v_v_2437_, 26);
v_homomulFn_x3f_2465_ = lean_ctor_get(v_v_2437_, 27);
v_subFn_2466_ = lean_ctor_get(v_v_2437_, 28);
v_negFn_2467_ = lean_ctor_get(v_v_2437_, 29);
v_vars_2468_ = lean_ctor_get(v_v_2437_, 30);
v_varMap_2469_ = lean_ctor_get(v_v_2437_, 31);
v_lowers_2470_ = lean_ctor_get(v_v_2437_, 32);
v_uppers_2471_ = lean_ctor_get(v_v_2437_, 33);
v_diseqs_2472_ = lean_ctor_get(v_v_2437_, 34);
v_assignment_2473_ = lean_ctor_get(v_v_2437_, 35);
v_caseSplits_2474_ = lean_ctor_get_uint8(v_v_2437_, sizeof(void*)*42);
v_conflict_x3f_2475_ = lean_ctor_get(v_v_2437_, 36);
v_diseqSplits_2476_ = lean_ctor_get(v_v_2437_, 37);
v_elimEqs_2477_ = lean_ctor_get(v_v_2437_, 38);
v_elimStack_2478_ = lean_ctor_get(v_v_2437_, 39);
v_occurs_2479_ = lean_ctor_get(v_v_2437_, 40);
v_ignored_2480_ = lean_ctor_get(v_v_2437_, 41);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_v_2437_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2482_ = v_v_2437_;
v_isShared_2483_ = v_isSharedCheck_2494_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_ignored_2480_);
lean_inc(v_occurs_2479_);
lean_inc(v_elimStack_2478_);
lean_inc(v_elimEqs_2477_);
lean_inc(v_diseqSplits_2476_);
lean_inc(v_conflict_x3f_2475_);
lean_inc(v_assignment_2473_);
lean_inc(v_diseqs_2472_);
lean_inc(v_uppers_2471_);
lean_inc(v_lowers_2470_);
lean_inc(v_varMap_2469_);
lean_inc(v_vars_2468_);
lean_inc(v_negFn_2467_);
lean_inc(v_subFn_2466_);
lean_inc(v_homomulFn_x3f_2465_);
lean_inc(v_nsmulFn_x3f_2464_);
lean_inc(v_zsmulFn_x3f_2463_);
lean_inc(v_nsmulFn_2462_);
lean_inc(v_zsmulFn_2461_);
lean_inc(v_addFn_2460_);
lean_inc(v_ltFn_x3f_2459_);
lean_inc(v_leFn_x3f_2458_);
lean_inc(v_one_x3f_2457_);
lean_inc(v_ofNatZero_2456_);
lean_inc(v_zero_2455_);
lean_inc(v_charInst_x3f_2454_);
lean_inc(v_fieldInst_x3f_2453_);
lean_inc(v_orderedRingInst_x3f_2452_);
lean_inc(v_commRingInst_x3f_2451_);
lean_inc(v_ringInst_x3f_2450_);
lean_inc(v_noNatDivInst_x3f_2449_);
lean_inc(v_isLinearInst_x3f_2448_);
lean_inc(v_orderedAddInst_x3f_2447_);
lean_inc(v_isPreorderInst_x3f_2446_);
lean_inc(v_lawfulOrderLTInst_x3f_2445_);
lean_inc(v_ltInst_x3f_2444_);
lean_inc(v_leInst_x3f_2443_);
lean_inc(v_intModuleInst_2442_);
lean_inc(v_u_2441_);
lean_inc(v_type_2440_);
lean_inc(v_ringId_x3f_2439_);
lean_inc(v_id_2438_);
lean_dec(v_v_2437_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2494_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v_xs_x27_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2484_ = lean_box(0);
v_xs_x27_2485_ = lean_array_fset(v_structs_2424_, v_a_2420_, v___x_2484_);
v___x_2486_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2421_, v_occurs_2479_, v_x_2422_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 40, v___x_2486_);
v___x_2488_ = v___x_2482_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_id_2438_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_ringId_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_type_2440_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_u_2441_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_intModuleInst_2442_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_leInst_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_ltInst_x3f_2444_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_lawfulOrderLTInst_x3f_2445_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_isPreorderInst_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_orderedAddInst_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2493_, 10, v_isLinearInst_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2493_, 11, v_noNatDivInst_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2493_, 12, v_ringInst_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2493_, 13, v_commRingInst_x3f_2451_);
lean_ctor_set(v_reuseFailAlloc_2493_, 14, v_orderedRingInst_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2493_, 15, v_fieldInst_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2493_, 16, v_charInst_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2493_, 17, v_zero_2455_);
lean_ctor_set(v_reuseFailAlloc_2493_, 18, v_ofNatZero_2456_);
lean_ctor_set(v_reuseFailAlloc_2493_, 19, v_one_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2493_, 20, v_leFn_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2493_, 21, v_ltFn_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2493_, 22, v_addFn_2460_);
lean_ctor_set(v_reuseFailAlloc_2493_, 23, v_zsmulFn_2461_);
lean_ctor_set(v_reuseFailAlloc_2493_, 24, v_nsmulFn_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 25, v_zsmulFn_x3f_2463_);
lean_ctor_set(v_reuseFailAlloc_2493_, 26, v_nsmulFn_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2493_, 27, v_homomulFn_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2493_, 28, v_subFn_2466_);
lean_ctor_set(v_reuseFailAlloc_2493_, 29, v_negFn_2467_);
lean_ctor_set(v_reuseFailAlloc_2493_, 30, v_vars_2468_);
lean_ctor_set(v_reuseFailAlloc_2493_, 31, v_varMap_2469_);
lean_ctor_set(v_reuseFailAlloc_2493_, 32, v_lowers_2470_);
lean_ctor_set(v_reuseFailAlloc_2493_, 33, v_uppers_2471_);
lean_ctor_set(v_reuseFailAlloc_2493_, 34, v_diseqs_2472_);
lean_ctor_set(v_reuseFailAlloc_2493_, 35, v_assignment_2473_);
lean_ctor_set(v_reuseFailAlloc_2493_, 36, v_conflict_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2493_, 37, v_diseqSplits_2476_);
lean_ctor_set(v_reuseFailAlloc_2493_, 38, v_elimEqs_2477_);
lean_ctor_set(v_reuseFailAlloc_2493_, 39, v_elimStack_2478_);
lean_ctor_set(v_reuseFailAlloc_2493_, 40, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2493_, 41, v_ignored_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*42, v_caseSplits_2474_);
v___x_2488_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_array_fset(v_xs_x27_2485_, v_a_2420_, v___x_2488_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2489_);
v___x_2491_ = v___x_2435_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_typeIdOf_2425_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_exprToStructId_2426_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_exprToStructIdEntries_2427_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_forbiddenNatModules_2428_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_natStructs_2429_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_natTypeIdOf_2430_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_exprToNatStructId_2431_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2504_, lean_object* v_y_2505_, lean_object* v_x_2506_, lean_object* v_s_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2504_, v_y_2505_, v_x_2506_, v_s_2507_);
lean_dec(v_x_2506_);
lean_dec(v_a_2504_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2509_, lean_object* v_y_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___f_2523_; lean_object* v___x_2524_; 
lean_inc(v_x_2509_);
lean_inc(v_y_2510_);
lean_inc(v_a_2511_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2523_, 0, v_a_2511_);
lean_closure_set(v___f_2523_, 1, v_y_2510_);
lean_closure_set(v___f_2523_, 2, v_x_2509_);
v___x_2524_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2509_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_x_2509_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2536_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2536_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2536_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v___x_2529_; 
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2510_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec(v_y_2510_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_del_object(v___x_2527_);
v___x_2530_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2531_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2530_, v___f_2523_, v_a_2512_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_dec_ref(v___f_2523_);
v___x_2532_ = lean_box(0);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2532_);
v___x_2534_ = v___x_2527_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___f_2523_);
lean_dec(v_y_2510_);
v_a_2537_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2524_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2524_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2545_, lean_object* v_y_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2545_, v_y_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec(v_a_2547_);
return v_res_2559_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2560_, lean_object* v_k_2561_, lean_object* v_t_2562_){
_start:
{
uint8_t v___x_2563_; 
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2561_, v_t_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2564_, lean_object* v_k_2565_, lean_object* v_t_2566_){
_start:
{
uint8_t v_res_2567_; lean_object* v_r_2568_; 
v_res_2567_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2564_, v_k_2565_, v_t_2566_);
lean_dec(v_t_2566_);
lean_dec(v_k_2565_);
v_r_2568_ = lean_box(v_res_2567_);
return v_r_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2569_, lean_object* v_k_2570_, lean_object* v_v_2571_, lean_object* v_t_2572_, lean_object* v_hl_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2570_, v_v_2571_, v_t_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2575_, lean_object* v_p_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
if (lean_obj_tag(v_p_2576_) == 1)
{
lean_object* v_v_2589_; lean_object* v_p_2590_; lean_object* v___x_2591_; 
v_v_2589_ = lean_ctor_get(v_p_2576_, 1);
lean_inc(v_v_2589_);
v_p_2590_ = lean_ctor_get(v_p_2576_, 2);
lean_inc(v_p_2590_);
lean_dec_ref_known(v_p_2576_, 3);
lean_inc(v_y_2575_);
v___x_2591_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2589_, v_y_2575_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v_p_2576_ = v_p_2590_;
goto _start;
}
else
{
lean_dec(v_p_2590_);
lean_dec(v_y_2575_);
return v___x_2591_;
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_p_2576_);
lean_dec(v_y_2575_);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2595_, lean_object* v_p_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2595_, v_p_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec(v_a_2597_);
return v_res_2609_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2612_ = l_Lean_stringToMessageData(v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
if (lean_obj_tag(v_p_2613_) == 1)
{
lean_object* v_v_2626_; lean_object* v_p_2627_; lean_object* v___x_2628_; 
v_v_2626_ = lean_ctor_get(v_p_2613_, 1);
lean_inc(v_v_2626_);
v_p_2627_ = lean_ctor_get(v_p_2613_, 2);
lean_inc(v_p_2627_);
lean_dec_ref_known(v_p_2613_, 3);
v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2626_, v_p_2627_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_p_2613_);
v___x_2629_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2630_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2629_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec(v_a_2632_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
if (lean_obj_tag(v_p_2645_) == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
else
{
lean_object* v_k_2660_; lean_object* v_v_2661_; lean_object* v_p_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_k_2660_ = lean_ctor_get(v_p_2645_, 0);
v_v_2661_ = lean_ctor_get(v_p_2645_, 1);
v_p_2662_ = lean_ctor_get(v_p_2645_, 2);
v___x_2663_ = lean_box(0);
v___x_2664_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2690_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___y_2670_; lean_object* v_elimEqs_2685_; lean_object* v_size_2686_; uint8_t v___x_2687_; 
v_elimEqs_2685_ = lean_ctor_get(v_a_2665_, 38);
lean_inc_ref(v_elimEqs_2685_);
lean_dec(v_a_2665_);
v_size_2686_ = lean_ctor_get(v_elimEqs_2685_, 2);
v___x_2687_ = lean_nat_dec_lt(v_v_2661_, v_size_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v_elimEqs_2685_);
v___x_2688_ = l_outOfBounds___redArg(v___x_2663_);
v___y_2670_ = v___x_2688_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2663_, v_elimEqs_2685_, v_v_2661_);
lean_dec_ref(v_elimEqs_2685_);
v___y_2670_ = v___x_2689_;
goto v___jp_2669_;
}
v___jp_2669_:
{
if (lean_obj_tag(v___y_2670_) == 1)
{
lean_object* v_val_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2683_; 
v_val_2671_ = lean_ctor_get(v___y_2670_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___y_2670_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2673_ = v___y_2670_;
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_val_2671_);
lean_dec(v___y_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2683_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
lean_inc(v_v_2661_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_v_2661_);
lean_ctor_set(v___x_2675_, 1, v_val_2671_);
lean_inc(v_k_2660_);
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_k_2660_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2676_);
v___x_2678_ = v___x_2673_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2678_);
v___x_2680_ = v___x_2667_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_dec(v___y_2670_);
lean_del_object(v___x_2667_);
v_p_2645_ = v_p_2662_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_a_2691_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2664_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2664_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec(v_p_2699_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
return v_x_2714_;
}
else
{
lean_object* v_k_2715_; lean_object* v_p_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_k_2715_ = lean_ctor_get(v_x_2713_, 0);
v_p_2716_ = lean_ctor_get(v_x_2713_, 2);
v___x_2717_ = lean_nat_to_int(v_x_2714_);
v___x_2718_ = l_Int_gcd(v_k_2715_, v___x_2717_);
lean_dec(v___x_2717_);
v_x_2713_ = v_p_2716_;
v_x_2714_ = v___x_2718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2720_, lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2720_, v_x_2721_);
lean_dec(v_x_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2723_){
_start:
{
if (lean_obj_tag(v_p_2723_) == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_unsigned_to_nat(1u);
return v___x_2724_;
}
else
{
lean_object* v_k_2725_; lean_object* v_p_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_k_2725_ = lean_ctor_get(v_p_2723_, 0);
v_p_2726_ = lean_ctor_get(v_p_2723_, 2);
v___x_2727_ = lean_nat_abs(v_k_2725_);
v___x_2728_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2726_, v___x_2727_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2729_);
lean_dec(v_p_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2731_, lean_object* v_k_2732_){
_start:
{
if (lean_obj_tag(v_p_2731_) == 0)
{
return v_p_2731_;
}
else
{
lean_object* v_k_2733_; lean_object* v_v_2734_; lean_object* v_p_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2744_; 
v_k_2733_ = lean_ctor_get(v_p_2731_, 0);
v_v_2734_ = lean_ctor_get(v_p_2731_, 1);
v_p_2735_ = lean_ctor_get(v_p_2731_, 2);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_p_2731_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2737_ = v_p_2731_;
v_isShared_2738_ = v_isSharedCheck_2744_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_p_2735_);
lean_inc(v_v_2734_);
lean_inc(v_k_2733_);
lean_dec(v_p_2731_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2744_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2739_ = lean_int_ediv(v_k_2733_, v_k_2732_);
lean_dec(v_k_2733_);
v___x_2740_ = l_Lean_Grind_Linarith_Poly_div(v_p_2735_, v_k_2732_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 2, v___x_2740_);
lean_ctor_set(v___x_2737_, 0, v___x_2739_);
v___x_2742_ = v___x_2737_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_v_2734_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2745_, lean_object* v_k_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Grind_Linarith_Poly_div(v_p_2745_, v_k_2746_);
lean_dec(v_k_2746_);
return v_res_2747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_unsigned_to_nat(1u);
v___x_2749_ = lean_nat_to_int(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2751_ = lean_int_neg(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2752_, lean_object* v_x_2753_, lean_object* v_p_2754_){
_start:
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2756_ = lean_int_dec_eq(v_k_2752_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2758_ = lean_int_dec_eq(v_k_2752_, v___x_2757_);
if (v___x_2758_ == 0)
{
if (lean_obj_tag(v_p_2754_) == 0)
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_k_2752_);
lean_ctor_set(v___x_2759_, 1, v_x_2753_);
return v___x_2759_;
}
else
{
lean_object* v_k_2760_; lean_object* v_v_2761_; lean_object* v_p_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_k_2760_ = lean_ctor_get(v_p_2754_, 0);
lean_inc(v_k_2760_);
v_v_2761_ = lean_ctor_get(v_p_2754_, 1);
lean_inc(v_v_2761_);
v_p_2762_ = lean_ctor_get(v_p_2754_, 2);
lean_inc(v_p_2762_);
lean_dec_ref_known(v_p_2754_, 3);
v___x_2763_ = lean_nat_abs(v_k_2760_);
v___x_2764_ = lean_nat_abs(v_k_2752_);
v___x_2765_ = lean_nat_dec_lt(v___x_2763_, v___x_2764_);
lean_dec(v___x_2764_);
lean_dec(v___x_2763_);
if (v___x_2765_ == 0)
{
lean_dec(v_v_2761_);
lean_dec(v_k_2760_);
v_p_2754_ = v_p_2762_;
goto _start;
}
else
{
lean_dec(v_x_2753_);
lean_dec(v_k_2752_);
v_k_2752_ = v_k_2760_;
v_x_2753_ = v_v_2761_;
v_p_2754_ = v_p_2762_;
goto _start;
}
}
}
else
{
lean_object* v___x_2768_; 
lean_dec(v_p_2754_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_k_2752_);
lean_ctor_set(v___x_2768_, 1, v_x_2753_);
return v___x_2768_;
}
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_p_2754_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_k_2752_);
lean_ctor_set(v___x_2769_, 1, v_x_2753_);
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2770_){
_start:
{
if (lean_obj_tag(v_p_2770_) == 0)
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
else
{
lean_object* v_k_2772_; lean_object* v_v_2773_; lean_object* v_p_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_k_2772_ = lean_ctor_get(v_p_2770_, 0);
lean_inc(v_k_2772_);
v_v_2773_ = lean_ctor_get(v_p_2770_, 1);
lean_inc(v_v_2773_);
v_p_2774_ = lean_ctor_get(v_p_2770_, 2);
lean_inc(v_p_2774_);
lean_dec_ref_known(v_p_2770_, 3);
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2772_, v_v_2773_, v_p_2774_);
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
}
#ifdef __cplusplus
}
#endif
