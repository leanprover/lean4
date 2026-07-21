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
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
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
lean_object* v_noNatDivInst_x3f_265_; 
v_noNatDivInst_x3f_265_ = lean_ctor_get(v_a_261_, 11);
lean_inc(v_noNatDivInst_x3f_265_);
lean_dec(v_a_261_);
if (lean_obj_tag(v_noNatDivInst_x3f_265_) == 0)
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
lean_dec_ref_known(v_noNatDivInst_x3f_265_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_i_300_, lean_object* v_k_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_array_get_size(v_keys_298_);
v___x_303_ = lean_nat_dec_lt(v_i_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v_i_300_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_k_x27_305_; size_t v___x_306_; size_t v___x_307_; uint8_t v___x_308_; 
v_k_x27_305_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v___x_306_ = lean_ptr_addr(v_k_301_);
v___x_307_ = lean_ptr_addr(v_k_x27_305_);
v___x_308_ = lean_usize_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_i_300_, v___x_309_);
lean_dec(v_i_300_);
v_i_300_ = v___x_310_;
goto _start;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
lean_dec(v_i_300_);
lean_inc(v___x_312_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_314_, lean_object* v_vals_315_, lean_object* v_i_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_314_, v_vals_315_, v_i_316_, v_k_317_);
lean_dec_ref(v_k_317_);
lean_dec_ref(v_vals_315_);
lean_dec_ref(v_keys_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_319_, size_t v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_es_322_; lean_object* v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v_j_326_; lean_object* v___x_327_; 
v_es_322_ = lean_ctor_get(v_x_319_, 0);
v___x_323_ = lean_box(2);
v___x_324_ = ((size_t)31ULL);
v___x_325_ = lean_usize_land(v_x_320_, v___x_324_);
v_j_326_ = lean_usize_to_nat(v___x_325_);
v___x_327_ = lean_array_get_borrowed(v___x_323_, v_es_322_, v_j_326_);
lean_dec(v_j_326_);
switch(lean_obj_tag(v___x_327_))
{
case 0:
{
lean_object* v_key_328_; lean_object* v_val_329_; size_t v___x_330_; size_t v___x_331_; uint8_t v___x_332_; 
v_key_328_ = lean_ctor_get(v___x_327_, 0);
v_val_329_ = lean_ctor_get(v___x_327_, 1);
v___x_330_ = lean_ptr_addr(v_x_321_);
v___x_331_ = lean_ptr_addr(v_key_328_);
v___x_332_ = lean_usize_dec_eq(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
lean_inc(v_val_329_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_val_329_);
return v___x_334_;
}
}
case 1:
{
lean_object* v_node_335_; size_t v___x_336_; size_t v___x_337_; 
v_node_335_ = lean_ctor_get(v___x_327_, 0);
v___x_336_ = ((size_t)5ULL);
v___x_337_ = lean_usize_shift_right(v_x_320_, v___x_336_);
v_x_319_ = v_node_335_;
v_x_320_ = v___x_337_;
goto _start;
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
}
}
else
{
lean_object* v_ks_340_; lean_object* v_vs_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_ks_340_ = lean_ctor_get(v_x_319_, 0);
v_vs_341_ = lean_ctor_get(v_x_319_, 1);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_340_, v_vs_341_, v___x_342_, v_x_321_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
size_t v_x_890__boxed_347_; lean_object* v_res_348_; 
v_x_890__boxed_347_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_res_348_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_344_, v_x_890__boxed_347_, v_x_346_);
lean_dec_ref(v_x_346_);
lean_dec_ref(v_x_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; uint64_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_ptr_addr(v_x_350_);
v___x_352_ = ((size_t)3ULL);
v___x_353_ = lean_usize_shift_right(v___x_351_, v___x_352_);
v___x_354_ = lean_usize_to_uint64(v___x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_349_, v___x_355_, v_x_350_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_357_, v_x_358_);
lean_dec_ref(v_x_358_);
lean_dec_ref(v_x_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_exprToStructId_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v_exprToStructId_369_ = lean_ctor_get(v_a_365_, 2);
lean_inc_ref(v_exprToStructId_369_);
lean_dec(v_a_365_);
v___x_370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_369_, v_e_360_);
lean_dec_ref(v_exprToStructId_369_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_364_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_364_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_383_, v_a_384_, v_a_385_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_e_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_388_, v_a_389_, v_a_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_e_401_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_418_, v_x_419_, v_x_420_);
lean_dec_ref(v_x_420_);
lean_dec_ref(v_x_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_422_, lean_object* v_x_423_, size_t v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_423_, v_x_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
size_t v_x_1011__boxed_431_; lean_object* v_res_432_; 
v_x_1011__boxed_431_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_427_, v_x_428_, v_x_1011__boxed_431_, v_x_430_);
lean_dec_ref(v_x_430_);
lean_dec_ref(v_x_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_434_, v_vals_435_, v_i_437_, v_k_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_440_, lean_object* v_keys_441_, lean_object* v_vals_442_, lean_object* v_heq_443_, lean_object* v_i_444_, lean_object* v_k_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_440_, v_keys_441_, v_vals_442_, v_heq_443_, v_i_444_, v_k_445_);
lean_dec_ref(v_k_445_);
lean_dec_ref(v_vals_442_);
lean_dec_ref(v_keys_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_ks_451_; lean_object* v_vs_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_478_; 
v_ks_451_ = lean_ctor_get(v_x_447_, 0);
v_vs_452_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_478_ == 0)
{
v___x_454_ = v_x_447_;
v_isShared_455_ = v_isSharedCheck_478_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_vs_452_);
lean_inc(v_ks_451_);
lean_dec(v_x_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_478_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_array_get_size(v_ks_451_);
v___x_457_ = lean_nat_dec_lt(v_x_448_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_x_448_);
v___x_458_ = lean_array_push(v_ks_451_, v_x_449_);
v___x_459_ = lean_array_push(v_vs_452_, v_x_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_459_);
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
else
{
lean_object* v_k_x27_463_; size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v_k_x27_463_ = lean_array_fget_borrowed(v_ks_451_, v_x_448_);
v___x_464_ = lean_ptr_addr(v_x_449_);
v___x_465_ = lean_ptr_addr(v_k_x27_463_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_468_; 
if (v_isShared_455_ == 0)
{
v___x_468_ = v___x_454_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_ks_451_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_vs_452_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_x_448_, v___x_469_);
lean_dec(v_x_448_);
v_x_447_ = v___x_468_;
v_x_448_ = v___x_470_;
goto _start;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_array_fset(v_ks_451_, v_x_448_, v_x_449_);
v___x_474_ = lean_array_fset(v_vs_452_, v_x_448_, v_x_450_);
lean_dec(v_x_448_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_474_);
lean_ctor_set(v___x_454_, 0, v___x_473_);
v___x_476_ = v___x_454_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_479_, lean_object* v_k_480_, lean_object* v_v_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_479_, v___x_482_, v_k_480_, v_v_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_485_, size_t v_x_486_, size_t v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_es_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v_j_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_es_490_ = lean_ctor_get(v_x_485_, 0);
v___x_491_ = ((size_t)31ULL);
v___x_492_ = lean_usize_land(v_x_486_, v___x_491_);
v_j_493_ = lean_usize_to_nat(v___x_492_);
v___x_494_ = lean_array_get_size(v_es_490_);
v___x_495_ = lean_nat_dec_lt(v_j_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v_j_493_);
lean_dec(v_x_489_);
lean_dec_ref(v_x_488_);
return v_x_485_;
}
else
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_536_; 
lean_inc_ref(v_es_490_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_x_485_, 0);
lean_dec(v_unused_537_);
v___x_497_ = v_x_485_;
v_isShared_498_ = v_isSharedCheck_536_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_x_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_536_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_v_499_; lean_object* v___x_500_; lean_object* v_xs_x27_501_; lean_object* v___y_503_; 
v_v_499_ = lean_array_fget(v_es_490_, v_j_493_);
v___x_500_ = lean_box(0);
v_xs_x27_501_ = lean_array_fset(v_es_490_, v_j_493_, v___x_500_);
switch(lean_obj_tag(v_v_499_))
{
case 0:
{
lean_object* v_key_508_; lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
v_key_508_ = lean_ctor_get(v_v_499_, 0);
v_val_509_ = lean_ctor_get(v_v_499_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_v_499_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v_v_499_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_inc(v_key_508_);
lean_dec(v_v_499_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_x_488_);
v___x_514_ = lean_ptr_addr(v_key_508_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_del_object(v___x_511_);
v___x_516_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_508_, v_val_509_, v_x_488_, v_x_489_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___y_503_ = v___x_517_;
goto v___jp_502_;
}
else
{
lean_object* v___x_519_; 
lean_dec(v_val_509_);
lean_dec(v_key_508_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_x_489_);
lean_ctor_set(v___x_511_, 0, v_x_488_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_x_488_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_x_489_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
v___y_503_ = v___x_519_;
goto v___jp_502_;
}
}
}
}
case 1:
{
lean_object* v_node_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_node_522_ = lean_ctor_get(v_v_499_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_v_499_);
if (v_isSharedCheck_534_ == 0)
{
v___x_524_ = v_v_499_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_node_522_);
lean_dec(v_v_499_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_526_ = ((size_t)5ULL);
v___x_527_ = lean_usize_shift_right(v_x_486_, v___x_526_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_x_487_, v___x_528_);
v___x_530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_522_, v___x_527_, v___x_529_, v_x_488_, v_x_489_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_530_);
v___x_532_ = v___x_524_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_503_ = v___x_532_;
goto v___jp_502_;
}
}
}
default: 
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_x_488_);
lean_ctor_set(v___x_535_, 1, v_x_489_);
v___y_503_ = v___x_535_;
goto v___jp_502_;
}
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_array_fset(v_xs_x27_501_, v_j_493_, v___y_503_);
lean_dec(v_j_493_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_504_);
v___x_506_ = v___x_497_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_538_; lean_object* v_vs_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_559_; 
v_ks_538_ = lean_ctor_get(v_x_485_, 0);
v_vs_539_ = lean_ctor_get(v_x_485_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_559_ == 0)
{
v___x_541_ = v_x_485_;
v_isShared_542_ = v_isSharedCheck_559_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_vs_539_);
lean_inc(v_ks_538_);
lean_dec(v_x_485_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_559_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_ks_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_vs_539_);
v___x_544_ = v_reuseFailAlloc_558_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v_newNode_545_; uint8_t v___y_547_; size_t v___x_553_; uint8_t v___x_554_; 
v_newNode_545_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_544_, v_x_488_, v_x_489_);
v___x_553_ = ((size_t)7ULL);
v___x_554_ = lean_usize_dec_le(v___x_553_, v_x_487_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_545_);
v___x_556_ = lean_unsigned_to_nat(4u);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
v___y_547_ = v___x_557_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v_ks_548_; lean_object* v_vs_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ks_548_ = lean_ctor_get(v_newNode_545_, 0);
lean_inc_ref(v_ks_548_);
v_vs_549_ = lean_ctor_get(v_newNode_545_, 1);
lean_inc_ref(v_vs_549_);
lean_dec_ref(v_newNode_545_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_487_, v_ks_548_, v_vs_549_, v___x_550_, v___x_551_);
lean_dec_ref(v_vs_549_);
lean_dec_ref(v_ks_548_);
return v___x_552_;
}
else
{
return v_newNode_545_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_560_, lean_object* v_keys_561_, lean_object* v_vals_562_, lean_object* v_i_563_, lean_object* v_entries_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_keys_561_);
v___x_566_ = lean_nat_dec_lt(v_i_563_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec(v_i_563_);
return v_entries_564_;
}
else
{
lean_object* v_k_567_; lean_object* v_v_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; uint64_t v___x_572_; size_t v_h_573_; size_t v___x_574_; lean_object* v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v_h_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_k_567_ = lean_array_fget_borrowed(v_keys_561_, v_i_563_);
v_v_568_ = lean_array_fget_borrowed(v_vals_562_, v_i_563_);
v___x_569_ = lean_ptr_addr(v_k_567_);
v___x_570_ = ((size_t)3ULL);
v___x_571_ = lean_usize_shift_right(v___x_569_, v___x_570_);
v___x_572_ = lean_usize_to_uint64(v___x_571_);
v_h_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = ((size_t)5ULL);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_sub(v_depth_560_, v___x_576_);
v___x_578_ = lean_usize_mul(v___x_574_, v___x_577_);
v_h_579_ = lean_usize_shift_right(v_h_573_, v___x_578_);
v___x_580_ = lean_nat_add(v_i_563_, v___x_575_);
lean_dec(v_i_563_);
lean_inc(v_v_568_);
lean_inc(v_k_567_);
v___x_581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_564_, v_h_579_, v_depth_560_, v_k_567_, v_v_568_);
v_i_563_ = v___x_580_;
v_entries_564_ = v___x_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_583_, lean_object* v_keys_584_, lean_object* v_vals_585_, lean_object* v_i_586_, lean_object* v_entries_587_){
_start:
{
size_t v_depth_boxed_588_; lean_object* v_res_589_; 
v_depth_boxed_588_ = lean_unbox_usize(v_depth_583_);
lean_dec(v_depth_583_);
v_res_589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_588_, v_keys_584_, v_vals_585_, v_i_586_, v_entries_587_);
lean_dec_ref(v_vals_585_);
lean_dec_ref(v_keys_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
size_t v_x_7055__boxed_595_; size_t v_x_7056__boxed_596_; lean_object* v_res_597_; 
v_x_7055__boxed_595_ = lean_unbox_usize(v_x_591_);
lean_dec(v_x_591_);
v_x_7056__boxed_596_ = lean_unbox_usize(v_x_592_);
lean_dec(v_x_592_);
v_res_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_590_, v_x_7055__boxed_595_, v_x_7056__boxed_596_, v_x_593_, v_x_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; uint64_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_601_ = lean_ptr_addr(v_x_599_);
v___x_602_ = ((size_t)3ULL);
v___x_603_ = lean_usize_shift_right(v___x_601_, v___x_602_);
v___x_604_ = lean_usize_to_uint64(v___x_603_);
v___x_605_ = lean_uint64_to_usize(v___x_604_);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_598_, v___x_605_, v___x_606_, v_x_599_, v_x_600_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_608_, lean_object* v_a_609_, lean_object* v_s_610_){
_start:
{
lean_object* v_structs_611_; lean_object* v_typeIdOf_612_; lean_object* v_exprToStructId_613_; lean_object* v_exprToStructIdEntries_614_; lean_object* v_forbiddenNatModules_615_; lean_object* v_natStructs_616_; lean_object* v_natTypeIdOf_617_; lean_object* v_exprToNatStructId_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_628_; 
v_structs_611_ = lean_ctor_get(v_s_610_, 0);
v_typeIdOf_612_ = lean_ctor_get(v_s_610_, 1);
v_exprToStructId_613_ = lean_ctor_get(v_s_610_, 2);
v_exprToStructIdEntries_614_ = lean_ctor_get(v_s_610_, 3);
v_forbiddenNatModules_615_ = lean_ctor_get(v_s_610_, 4);
v_natStructs_616_ = lean_ctor_get(v_s_610_, 5);
v_natTypeIdOf_617_ = lean_ctor_get(v_s_610_, 6);
v_exprToNatStructId_618_ = lean_ctor_get(v_s_610_, 7);
v_isSharedCheck_628_ = !lean_is_exclusive(v_s_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_620_ = v_s_610_;
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_exprToNatStructId_618_);
lean_inc(v_natTypeIdOf_617_);
lean_inc(v_natStructs_616_);
lean_inc(v_forbiddenNatModules_615_);
lean_inc(v_exprToStructIdEntries_614_);
lean_inc(v_exprToStructId_613_);
lean_inc(v_typeIdOf_612_);
lean_inc(v_structs_611_);
lean_dec(v_s_610_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_inc_n(v_a_609_, 2);
lean_inc_ref(v_e_608_);
v___x_622_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_613_, v_e_608_, v_a_609_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_e_608_);
lean_ctor_set(v___x_623_, 1, v_a_609_);
v___x_624_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_614_, v___x_623_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 3, v___x_624_);
lean_ctor_set(v___x_620_, 2, v___x_622_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_structs_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_typeIdOf_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_forbiddenNatModules_615_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_natStructs_616_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_natTypeIdOf_617_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_exprToNatStructId_618_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_629_, lean_object* v_a_630_, lean_object* v_s_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_629_, v_a_630_, v_s_631_);
lean_dec(v_a_630_);
return v_res_632_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_636_, v_a_638_, v_a_643_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
if (lean_obj_tag(v_a_650_) == 1)
{
lean_object* v_val_651_; uint8_t v___x_652_; 
v_val_651_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v_a_650_, 1);
v___x_652_ = lean_nat_dec_eq(v_val_651_, v_a_637_);
lean_dec(v_val_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_639_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v_verbose_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v_verbose_655_ = lean_ctor_get_uint8(v_a_654_, 0);
lean_dec(v_a_654_);
if (v_verbose_655_ == 0)
{
lean_dec_ref(v_e_636_);
goto v___jp_646_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_657_ = l_Lean_indentExpr(v_e_636_);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_Meta_Sym_reportIssue(v___x_658_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_dec_ref_known(v___x_659_, 1);
goto v___jp_646_;
}
else
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_e_636_);
v_a_660_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_653_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_653_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
lean_dec_ref(v_e_636_);
goto v___jp_646_;
}
}
else
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_a_650_);
lean_inc(v_a_637_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_668_, 0, v_e_636_);
lean_closure_set(v___f_668_, 1, v_a_637_);
v___x_669_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_670_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_669_, v___f_668_, v_a_638_);
return v___x_670_;
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_e_636_);
v_a_671_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_649_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_649_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
v___jp_646_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec(v_a_680_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_690_, v_a_691_, v_a_692_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_719_, v_x_720_, v_x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_723_, lean_object* v_x_724_, size_t v_x_725_, size_t v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_724_, v_x_725_, v_x_726_, v_x_727_, v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
size_t v_x_7349__boxed_736_; size_t v_x_7350__boxed_737_; lean_object* v_res_738_; 
v_x_7349__boxed_736_ = lean_unbox_usize(v_x_732_);
lean_dec(v_x_732_);
v_x_7350__boxed_737_ = lean_unbox_usize(v_x_733_);
lean_dec(v_x_733_);
v_res_738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_730_, v_x_731_, v_x_7349__boxed_736_, v_x_7350__boxed_737_, v_x_734_, v_x_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_739_, lean_object* v_n_740_, lean_object* v_k_741_, lean_object* v_v_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_740_, v_k_741_, v_v_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_744_, size_t v_depth_745_, lean_object* v_keys_746_, lean_object* v_vals_747_, lean_object* v_heq_748_, lean_object* v_i_749_, lean_object* v_entries_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_745_, v_keys_746_, v_vals_747_, v_i_749_, v_entries_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_752_, lean_object* v_depth_753_, lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_heq_756_, lean_object* v_i_757_, lean_object* v_entries_758_){
_start:
{
size_t v_depth_boxed_759_; lean_object* v_res_760_; 
v_depth_boxed_759_ = lean_unbox_usize(v_depth_753_);
lean_dec(v_depth_753_);
v_res_760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_752_, v_depth_boxed_759_, v_keys_754_, v_vals_755_, v_heq_756_, v_i_757_, v_entries_758_);
lean_dec_ref(v_vals_755_);
lean_dec_ref(v_keys_754_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_762_, v_x_763_, v_x_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_env_774_; lean_object* v___x_775_; lean_object* v_mctx_776_; lean_object* v_lctx_777_; lean_object* v_options_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_773_ = lean_st_ref_get(v___y_771_);
v_env_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc_ref(v_env_774_);
lean_dec(v___x_773_);
v___x_775_ = lean_st_ref_get(v___y_769_);
v_mctx_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_ref(v_mctx_776_);
lean_dec(v___x_775_);
v_lctx_777_ = lean_ctor_get(v___y_768_, 2);
v_options_778_ = lean_ctor_get(v___y_770_, 2);
lean_inc_ref(v_options_778_);
lean_inc_ref(v_lctx_777_);
v___x_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_779_, 0, v_env_774_);
lean_ctor_set(v___x_779_, 1, v_mctx_776_);
lean_ctor_set(v___x_779_, 2, v_lctx_777_);
lean_ctor_set(v___x_779_, 3, v_options_778_);
v___x_780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_msgData_767_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_ref_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_ref_795_ = lean_ctor_get(v___y_792_, 5);
v___x_796_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_ref_795_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_ref_795_);
lean_ctor_set(v___x_801_, 1, v_a_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 1);
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_840_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_840_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_840_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_noNatDivInst_x3f_833_; 
v_noNatDivInst_x3f_833_ = lean_ctor_get(v_a_829_, 11);
lean_inc(v_noNatDivInst_x3f_833_);
lean_dec(v_a_829_);
if (lean_obj_tag(v_noNatDivInst_x3f_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_836_; 
v_val_834_ = lean_ctor_get(v_noNatDivInst_x3f_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_noNatDivInst_x3f_833_, 1);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_val_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_val_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v_noNatDivInst_x3f_833_);
lean_del_object(v___x_831_);
v___x_838_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_839_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_838_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_839_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_828_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_828_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_862_, lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_863_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_877_, v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_919_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_leInst_x3f_912_; 
v_leInst_x3f_912_ = lean_ctor_get(v_a_908_, 5);
lean_inc(v_leInst_x3f_912_);
lean_dec(v_a_908_);
if (lean_obj_tag(v_leInst_x3f_912_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_915_; 
v_val_913_ = lean_ctor_get(v_leInst_x3f_912_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v_leInst_x3f_912_, 1);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_val_913_);
v___x_915_ = v___x_910_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_val_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_leInst_x3f_912_);
lean_del_object(v___x_910_);
v___x_917_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_918_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_917_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_918_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_907_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_907_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec(v_a_929_);
lean_dec(v_a_928_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_968_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_968_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_ltInst_x3f_961_; 
v_ltInst_x3f_961_ = lean_ctor_get(v_a_957_, 6);
lean_inc(v_ltInst_x3f_961_);
lean_dec(v_a_957_);
if (lean_obj_tag(v_ltInst_x3f_961_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; 
v_val_962_ = lean_ctor_get(v_ltInst_x3f_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v_ltInst_x3f_961_, 1);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_val_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_val_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v_ltInst_x3f_961_);
lean_del_object(v___x_959_);
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_967_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_966_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
return v___x_967_;
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_956_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_956_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_lawfulOrderLTInst_x3f_1010_; 
v_lawfulOrderLTInst_x3f_1010_ = lean_ctor_get(v_a_1006_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1010_);
lean_dec(v_a_1006_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1010_) == 1)
{
lean_object* v_val_1011_; lean_object* v___x_1013_; 
v_val_1011_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1010_, 1);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v_val_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_val_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_lawfulOrderLTInst_x3f_1010_);
lean_del_object(v___x_1008_);
v___x_1015_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1016_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1015_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1005_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1005_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec(v_a_1026_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1066_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1066_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_isPreorderInst_x3f_1059_; 
v_isPreorderInst_x3f_1059_ = lean_ctor_get(v_a_1055_, 8);
lean_inc(v_isPreorderInst_x3f_1059_);
lean_dec(v_a_1055_);
if (lean_obj_tag(v_isPreorderInst_x3f_1059_) == 1)
{
lean_object* v_val_1060_; lean_object* v___x_1062_; 
v_val_1060_ = lean_ctor_get(v_isPreorderInst_x3f_1059_, 0);
lean_inc(v_val_1060_);
lean_dec_ref_known(v_isPreorderInst_x3f_1059_, 1);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v_val_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_isPreorderInst_x3f_1059_);
lean_del_object(v___x_1057_);
v___x_1064_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1065_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1064_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1054_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1054_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec(v_a_1075_);
return v_res_1087_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1115_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_orderedAddInst_x3f_1108_; 
v_orderedAddInst_x3f_1108_ = lean_ctor_get(v_a_1104_, 9);
lean_inc(v_orderedAddInst_x3f_1108_);
lean_dec(v_a_1104_);
if (lean_obj_tag(v_orderedAddInst_x3f_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v___x_1111_; 
v_val_1109_ = lean_ctor_get(v_orderedAddInst_x3f_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v_orderedAddInst_x3f_1108_, 1);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_val_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_val_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v_orderedAddInst_x3f_1108_);
lean_del_object(v___x_1106_);
v___x_1113_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1114_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1113_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1103_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1103_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec(v_a_1124_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1165_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1165_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1165_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_orderedAddInst_x3f_1154_; 
v_orderedAddInst_x3f_1154_ = lean_ctor_get(v_a_1150_, 9);
lean_inc(v_orderedAddInst_x3f_1154_);
lean_dec(v_a_1150_);
if (lean_obj_tag(v_orderedAddInst_x3f_1154_) == 0)
{
uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1155_ = 0;
v___x_1156_ = lean_box(v___x_1155_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1156_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_dec_ref_known(v_orderedAddInst_x3f_1154_, 1);
v___x_1160_ = 1;
v___x_1161_ = lean_box(v___x_1160_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1161_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1149_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1149_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec(v_a_1174_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_____do__lift_1190_){
_start:
{
lean_object* v_ltFn_x3f_1191_; 
v_ltFn_x3f_1191_ = lean_ctor_get(v_____do__lift_1190_, 21);
lean_inc(v_ltFn_x3f_1191_);
lean_dec_ref(v_____do__lift_1190_);
if (lean_obj_tag(v_ltFn_x3f_1191_) == 1)
{
lean_object* v_val_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_inst_1189_);
lean_dec_ref(v_inst_1188_);
v_val_1192_ = lean_ctor_get(v_ltFn_x3f_1191_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_ltFn_x3f_1191_, 1);
v___x_1193_ = lean_apply_2(v_toPure_1187_, lean_box(0), v_val_1192_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_ltFn_x3f_1191_);
lean_dec(v_toPure_1187_);
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1195_ = l_Lean_throwError___redArg(v_inst_1188_, v_inst_1189_, v___x_1194_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v_toApplicative_1199_; lean_object* v_toBind_1200_; lean_object* v_toPure_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_toApplicative_1199_ = lean_ctor_get(v_inst_1196_, 0);
v_toBind_1200_ = lean_ctor_get(v_inst_1196_, 1);
lean_inc(v_toBind_1200_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1199_, 1);
lean_inc(v_toPure_1201_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1202_, 0, v_toPure_1201_);
lean_closure_set(v___f_1202_, 1, v_inst_1196_);
lean_closure_set(v___f_1202_, 2, v_inst_1197_);
v___x_1203_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v_inst_1198_, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1205_, v_inst_1206_, v_inst_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_____do__lift_1215_){
_start:
{
lean_object* v_leFn_x3f_1216_; 
v_leFn_x3f_1216_ = lean_ctor_get(v_____do__lift_1215_, 20);
lean_inc(v_leFn_x3f_1216_);
lean_dec_ref(v_____do__lift_1215_);
if (lean_obj_tag(v_leFn_x3f_1216_) == 1)
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_inst_1214_);
lean_dec_ref(v_inst_1213_);
v_val_1217_ = lean_ctor_get(v_leFn_x3f_1216_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_leFn_x3f_1216_, 1);
v___x_1218_ = lean_apply_2(v_toPure_1212_, lean_box(0), v_val_1217_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec(v_leFn_x3f_1216_);
lean_dec(v_toPure_1212_);
v___x_1219_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1220_ = l_Lean_throwError___redArg(v_inst_1213_, v_inst_1214_, v___x_1219_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v_toApplicative_1224_; lean_object* v_toBind_1225_; lean_object* v_toPure_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v_toApplicative_1224_ = lean_ctor_get(v_inst_1221_, 0);
v_toBind_1225_ = lean_ctor_get(v_inst_1221_, 1);
lean_inc(v_toBind_1225_);
v_toPure_1226_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_inc(v_toPure_1226_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1227_, 0, v_toPure_1226_);
lean_closure_set(v___f_1227_, 1, v_inst_1221_);
lean_closure_set(v___f_1227_, 2, v_inst_1222_);
v___x_1228_ = lean_apply_4(v_toBind_1225_, lean_box(0), lean_box(0), v_inst_1223_, v___f_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1230_, v_inst_1231_, v_inst_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1261_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1261_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_isLinearInst_x3f_1254_; 
v_isLinearInst_x3f_1254_ = lean_ctor_get(v_a_1250_, 10);
lean_inc(v_isLinearInst_x3f_1254_);
lean_dec(v_a_1250_);
if (lean_obj_tag(v_isLinearInst_x3f_1254_) == 1)
{
lean_object* v_val_1255_; lean_object* v___x_1257_; 
v_val_1255_ = lean_ctor_get(v_isLinearInst_x3f_1254_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v_isLinearInst_x3f_1254_, 1);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_val_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_val_1255_);
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
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_isLinearInst_x3f_1254_);
lean_del_object(v___x_1252_);
v___x_1259_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1260_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1259_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
v_a_1262_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1249_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1249_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1310_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1310_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1310_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_ringInst_x3f_1303_; 
v_ringInst_x3f_1303_ = lean_ctor_get(v_a_1299_, 12);
lean_inc(v_ringInst_x3f_1303_);
lean_dec(v_a_1299_);
if (lean_obj_tag(v_ringInst_x3f_1303_) == 1)
{
lean_object* v_val_1304_; lean_object* v___x_1306_; 
v_val_1304_ = lean_ctor_get(v_ringInst_x3f_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v_ringInst_x3f_1303_, 1);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_val_1304_);
v___x_1306_ = v___x_1301_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_val_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v_ringInst_x3f_1303_);
lean_del_object(v___x_1301_);
v___x_1308_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1309_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1308_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1298_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1298_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec(v_a_1319_);
return v_res_1331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_commRingInst_x3f_1352_; 
v_commRingInst_x3f_1352_ = lean_ctor_get(v_a_1348_, 13);
lean_inc(v_commRingInst_x3f_1352_);
lean_dec(v_a_1348_);
if (lean_obj_tag(v_commRingInst_x3f_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
v_val_1353_ = lean_ctor_get(v_commRingInst_x3f_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_commRingInst_x3f_1352_, 1);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_val_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_val_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_commRingInst_x3f_1352_);
lean_del_object(v___x_1350_);
v___x_1357_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1358_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1357_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1347_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1347_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec(v_a_1368_);
return v_res_1380_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_orderedRingInst_x3f_1401_; 
v_orderedRingInst_x3f_1401_ = lean_ctor_get(v_a_1397_, 14);
lean_inc(v_orderedRingInst_x3f_1401_);
lean_dec(v_a_1397_);
if (lean_obj_tag(v_orderedRingInst_x3f_1401_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1404_; 
v_val_1402_ = lean_ctor_get(v_orderedRingInst_x3f_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_orderedRingInst_x3f_1401_, 1);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_val_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_val_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v_orderedRingInst_x3f_1401_);
lean_del_object(v___x_1399_);
v___x_1406_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1407_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1406_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1396_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1396_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec(v_a_1417_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Rat_ofInt(v_a_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1432_, lean_object* v_v_1433_, lean_object* v_a_1434_){
_start:
{
if (lean_obj_tag(v_a_1434_) == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_v_1433_);
return v___x_1435_;
}
else
{
lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_p_1438_; lean_object* v_size_1439_; uint8_t v___x_1440_; 
v_k_1436_ = lean_ctor_get(v_a_1434_, 0);
lean_inc(v_k_1436_);
v_v_1437_ = lean_ctor_get(v_a_1434_, 1);
lean_inc(v_v_1437_);
v_p_1438_ = lean_ctor_get(v_a_1434_, 2);
lean_inc(v_p_1438_);
lean_dec_ref_known(v_a_1434_, 3);
v_size_1439_ = lean_ctor_get(v_a_1432_, 2);
v___x_1440_ = lean_nat_dec_lt(v_v_1437_, v_size_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_dec(v_p_1438_);
lean_dec(v_v_1437_);
lean_dec(v_k_1436_);
lean_dec_ref(v_v_1433_);
v___x_1441_ = lean_box(0);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1442_ = l_Rat_ofInt(v_k_1436_);
v___x_1443_ = l_instInhabitedRat;
v___x_1444_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1443_, v_a_1432_, v_v_1437_);
lean_dec(v_v_1437_);
v___x_1445_ = l_Rat_mul(v___x_1442_, v___x_1444_);
lean_dec_ref(v___x_1442_);
v___x_1446_ = l_Rat_add(v_v_1433_, v___x_1445_);
v_v_1433_ = v___x_1446_;
v_a_1434_ = v_p_1438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1448_, lean_object* v_v_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1448_, v_v_1449_, v_a_1450_);
lean_dec_ref(v_a_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_nat_to_int(v_a_1452_);
v___x_1454_ = l_Rat_ofInt(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_assignment_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v_assignment_1475_ = lean_ctor_get(v_a_1471_, 35);
lean_inc_ref(v_assignment_1475_);
lean_dec(v_a_1471_);
v___x_1476_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1475_, v___x_1476_, v_p_1457_);
lean_dec_ref(v_assignment_1475_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_p_1457_);
v_a_1482_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1470_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1470_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_nat_to_int(v_a_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_p_1519_; uint8_t v_strict_1520_; lean_object* v___x_1521_; 
v_p_1519_ = lean_ctor_get(v_c_1506_, 0);
lean_inc(v_p_1519_);
v_strict_1520_ = lean_ctor_get_uint8(v_c_1506_, sizeof(void*)*2);
lean_dec_ref(v_c_1506_);
v___x_1521_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1519_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1547_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1547_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1547_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
if (lean_obj_tag(v_a_1522_) == 1)
{
if (v_strict_1520_ == 0)
{
lean_object* v_val_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v_val_1526_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v_a_1522_, 1);
v___x_1527_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1528_ = l_Rat_instDecidableLe(v_val_1526_, v___x_1527_);
v___x_1529_ = l_Lean_Bool_toLBool(v___x_1528_);
v___x_1530_ = lean_box(v___x_1529_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1530_);
v___x_1532_ = v___x_1524_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v_val_1534_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v_a_1522_, 1);
v___x_1535_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1536_ = l_Rat_blt(v_val_1534_, v___x_1535_);
v___x_1537_ = l_Lean_Bool_toLBool(v___x_1536_);
v___x_1538_ = lean_box(v___x_1537_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1538_);
v___x_1540_ = v___x_1524_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_dec(v_a_1522_);
v___x_1542_ = 2;
v___x_1543_ = lean_box(v___x_1542_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1543_);
v___x_1545_ = v___x_1524_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
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
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1521_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1521_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec(v_a_1557_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_p_1583_; lean_object* v___x_1584_; 
v_p_1583_ = lean_ctor_get(v_c_1570_, 0);
lean_inc(v_p_1583_);
lean_dec_ref(v_c_1570_);
v___x_1584_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1583_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1604_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1604_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1604_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
uint8_t v___y_1590_; 
if (lean_obj_tag(v_a_1585_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_val_1596_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_a_1585_, 1);
v___x_1597_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1598_ = l_instDecidableEqRat_decEq(v_val_1596_, v___x_1597_);
lean_dec(v_val_1596_);
if (v___x_1598_ == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = 1;
v___y_1590_ = v___x_1599_;
goto v___jp_1589_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = 0;
v___y_1590_ = v___x_1600_;
goto v___jp_1589_;
}
}
else
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1587_);
lean_dec(v_a_1585_);
v___x_1601_ = 2;
v___x_1602_ = lean_box(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
v___jp_1589_:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_Bool_toLBool(v___y_1590_);
v___x_1592_ = lean_box(v___x_1591_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1592_);
v___x_1594_ = v___x_1587_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1584_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1584_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec(v_a_1614_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1627_, lean_object* v_x_1628_, lean_object* v_s_1629_){
_start:
{
lean_object* v_structs_1630_; lean_object* v_typeIdOf_1631_; lean_object* v_exprToStructId_1632_; lean_object* v_exprToStructIdEntries_1633_; lean_object* v_forbiddenNatModules_1634_; lean_object* v_natStructs_1635_; lean_object* v_natTypeIdOf_1636_; lean_object* v_exprToNatStructId_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_structs_1630_ = lean_ctor_get(v_s_1629_, 0);
v_typeIdOf_1631_ = lean_ctor_get(v_s_1629_, 1);
v_exprToStructId_1632_ = lean_ctor_get(v_s_1629_, 2);
v_exprToStructIdEntries_1633_ = lean_ctor_get(v_s_1629_, 3);
v_forbiddenNatModules_1634_ = lean_ctor_get(v_s_1629_, 4);
v_natStructs_1635_ = lean_ctor_get(v_s_1629_, 5);
v_natTypeIdOf_1636_ = lean_ctor_get(v_s_1629_, 6);
v_exprToNatStructId_1637_ = lean_ctor_get(v_s_1629_, 7);
v___x_1638_ = lean_array_get_size(v_structs_1630_);
v___x_1639_ = lean_nat_dec_lt(v_a_1627_, v___x_1638_);
if (v___x_1639_ == 0)
{
return v_s_1629_;
}
else
{
lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1701_; 
lean_inc_ref(v_exprToNatStructId_1637_);
lean_inc_ref(v_natTypeIdOf_1636_);
lean_inc_ref(v_natStructs_1635_);
lean_inc_ref(v_forbiddenNatModules_1634_);
lean_inc_ref(v_exprToStructIdEntries_1633_);
lean_inc_ref(v_exprToStructId_1632_);
lean_inc_ref(v_typeIdOf_1631_);
lean_inc_ref(v_structs_1630_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_s_1629_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1702_ = lean_ctor_get(v_s_1629_, 7);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_s_1629_, 6);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_s_1629_, 5);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_s_1629_, 4);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_s_1629_, 3);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_s_1629_, 2);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_s_1629_, 1);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_s_1629_, 0);
lean_dec(v_unused_1709_);
v___x_1641_ = v_s_1629_;
v_isShared_1642_ = v_isSharedCheck_1701_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_s_1629_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1701_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_v_1643_; lean_object* v_id_1644_; lean_object* v_ringId_x3f_1645_; lean_object* v_type_1646_; lean_object* v_u_1647_; lean_object* v_intModuleInst_1648_; lean_object* v_leInst_x3f_1649_; lean_object* v_ltInst_x3f_1650_; lean_object* v_lawfulOrderLTInst_x3f_1651_; lean_object* v_isPreorderInst_x3f_1652_; lean_object* v_orderedAddInst_x3f_1653_; lean_object* v_isLinearInst_x3f_1654_; lean_object* v_noNatDivInst_x3f_1655_; lean_object* v_ringInst_x3f_1656_; lean_object* v_commRingInst_x3f_1657_; lean_object* v_orderedRingInst_x3f_1658_; lean_object* v_fieldInst_x3f_1659_; lean_object* v_charInst_x3f_1660_; lean_object* v_zero_1661_; lean_object* v_ofNatZero_1662_; lean_object* v_one_x3f_1663_; lean_object* v_leFn_x3f_1664_; lean_object* v_ltFn_x3f_1665_; lean_object* v_addFn_1666_; lean_object* v_zsmulFn_1667_; lean_object* v_nsmulFn_1668_; lean_object* v_zsmulFn_x3f_1669_; lean_object* v_nsmulFn_x3f_1670_; lean_object* v_homomulFn_x3f_1671_; lean_object* v_subFn_1672_; lean_object* v_negFn_1673_; lean_object* v_vars_1674_; lean_object* v_varMap_1675_; lean_object* v_lowers_1676_; lean_object* v_uppers_1677_; lean_object* v_diseqs_1678_; lean_object* v_assignment_1679_; uint8_t v_caseSplits_1680_; lean_object* v_conflict_x3f_1681_; lean_object* v_diseqSplits_1682_; lean_object* v_elimEqs_1683_; lean_object* v_elimStack_1684_; lean_object* v_occurs_1685_; lean_object* v_ignored_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1700_; 
v_v_1643_ = lean_array_fget(v_structs_1630_, v_a_1627_);
v_id_1644_ = lean_ctor_get(v_v_1643_, 0);
v_ringId_x3f_1645_ = lean_ctor_get(v_v_1643_, 1);
v_type_1646_ = lean_ctor_get(v_v_1643_, 2);
v_u_1647_ = lean_ctor_get(v_v_1643_, 3);
v_intModuleInst_1648_ = lean_ctor_get(v_v_1643_, 4);
v_leInst_x3f_1649_ = lean_ctor_get(v_v_1643_, 5);
v_ltInst_x3f_1650_ = lean_ctor_get(v_v_1643_, 6);
v_lawfulOrderLTInst_x3f_1651_ = lean_ctor_get(v_v_1643_, 7);
v_isPreorderInst_x3f_1652_ = lean_ctor_get(v_v_1643_, 8);
v_orderedAddInst_x3f_1653_ = lean_ctor_get(v_v_1643_, 9);
v_isLinearInst_x3f_1654_ = lean_ctor_get(v_v_1643_, 10);
v_noNatDivInst_x3f_1655_ = lean_ctor_get(v_v_1643_, 11);
v_ringInst_x3f_1656_ = lean_ctor_get(v_v_1643_, 12);
v_commRingInst_x3f_1657_ = lean_ctor_get(v_v_1643_, 13);
v_orderedRingInst_x3f_1658_ = lean_ctor_get(v_v_1643_, 14);
v_fieldInst_x3f_1659_ = lean_ctor_get(v_v_1643_, 15);
v_charInst_x3f_1660_ = lean_ctor_get(v_v_1643_, 16);
v_zero_1661_ = lean_ctor_get(v_v_1643_, 17);
v_ofNatZero_1662_ = lean_ctor_get(v_v_1643_, 18);
v_one_x3f_1663_ = lean_ctor_get(v_v_1643_, 19);
v_leFn_x3f_1664_ = lean_ctor_get(v_v_1643_, 20);
v_ltFn_x3f_1665_ = lean_ctor_get(v_v_1643_, 21);
v_addFn_1666_ = lean_ctor_get(v_v_1643_, 22);
v_zsmulFn_1667_ = lean_ctor_get(v_v_1643_, 23);
v_nsmulFn_1668_ = lean_ctor_get(v_v_1643_, 24);
v_zsmulFn_x3f_1669_ = lean_ctor_get(v_v_1643_, 25);
v_nsmulFn_x3f_1670_ = lean_ctor_get(v_v_1643_, 26);
v_homomulFn_x3f_1671_ = lean_ctor_get(v_v_1643_, 27);
v_subFn_1672_ = lean_ctor_get(v_v_1643_, 28);
v_negFn_1673_ = lean_ctor_get(v_v_1643_, 29);
v_vars_1674_ = lean_ctor_get(v_v_1643_, 30);
v_varMap_1675_ = lean_ctor_get(v_v_1643_, 31);
v_lowers_1676_ = lean_ctor_get(v_v_1643_, 32);
v_uppers_1677_ = lean_ctor_get(v_v_1643_, 33);
v_diseqs_1678_ = lean_ctor_get(v_v_1643_, 34);
v_assignment_1679_ = lean_ctor_get(v_v_1643_, 35);
v_caseSplits_1680_ = lean_ctor_get_uint8(v_v_1643_, sizeof(void*)*42);
v_conflict_x3f_1681_ = lean_ctor_get(v_v_1643_, 36);
v_diseqSplits_1682_ = lean_ctor_get(v_v_1643_, 37);
v_elimEqs_1683_ = lean_ctor_get(v_v_1643_, 38);
v_elimStack_1684_ = lean_ctor_get(v_v_1643_, 39);
v_occurs_1685_ = lean_ctor_get(v_v_1643_, 40);
v_ignored_1686_ = lean_ctor_get(v_v_1643_, 41);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_v_1643_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1688_ = v_v_1643_;
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_ignored_1686_);
lean_inc(v_occurs_1685_);
lean_inc(v_elimStack_1684_);
lean_inc(v_elimEqs_1683_);
lean_inc(v_diseqSplits_1682_);
lean_inc(v_conflict_x3f_1681_);
lean_inc(v_assignment_1679_);
lean_inc(v_diseqs_1678_);
lean_inc(v_uppers_1677_);
lean_inc(v_lowers_1676_);
lean_inc(v_varMap_1675_);
lean_inc(v_vars_1674_);
lean_inc(v_negFn_1673_);
lean_inc(v_subFn_1672_);
lean_inc(v_homomulFn_x3f_1671_);
lean_inc(v_nsmulFn_x3f_1670_);
lean_inc(v_zsmulFn_x3f_1669_);
lean_inc(v_nsmulFn_1668_);
lean_inc(v_zsmulFn_1667_);
lean_inc(v_addFn_1666_);
lean_inc(v_ltFn_x3f_1665_);
lean_inc(v_leFn_x3f_1664_);
lean_inc(v_one_x3f_1663_);
lean_inc(v_ofNatZero_1662_);
lean_inc(v_zero_1661_);
lean_inc(v_charInst_x3f_1660_);
lean_inc(v_fieldInst_x3f_1659_);
lean_inc(v_orderedRingInst_x3f_1658_);
lean_inc(v_commRingInst_x3f_1657_);
lean_inc(v_ringInst_x3f_1656_);
lean_inc(v_noNatDivInst_x3f_1655_);
lean_inc(v_isLinearInst_x3f_1654_);
lean_inc(v_orderedAddInst_x3f_1653_);
lean_inc(v_isPreorderInst_x3f_1652_);
lean_inc(v_lawfulOrderLTInst_x3f_1651_);
lean_inc(v_ltInst_x3f_1650_);
lean_inc(v_leInst_x3f_1649_);
lean_inc(v_intModuleInst_1648_);
lean_inc(v_u_1647_);
lean_inc(v_type_1646_);
lean_inc(v_ringId_x3f_1645_);
lean_inc(v_id_1644_);
lean_dec(v_v_1643_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v_xs_x27_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1690_ = lean_box(0);
v_xs_x27_1691_ = lean_array_fset(v_structs_1630_, v_a_1627_, v___x_1690_);
v___x_1692_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1679_, v_x_1628_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 35, v___x_1692_);
v___x_1694_ = v___x_1688_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_id_1644_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_ringId_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_type_1646_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_u_1647_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_intModuleInst_1648_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_leInst_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_ltInst_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_lawfulOrderLTInst_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v_isPreorderInst_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_orderedAddInst_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1699_, 10, v_isLinearInst_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1699_, 11, v_noNatDivInst_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1699_, 12, v_ringInst_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1699_, 13, v_commRingInst_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1699_, 14, v_orderedRingInst_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1699_, 15, v_fieldInst_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1699_, 16, v_charInst_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1699_, 17, v_zero_1661_);
lean_ctor_set(v_reuseFailAlloc_1699_, 18, v_ofNatZero_1662_);
lean_ctor_set(v_reuseFailAlloc_1699_, 19, v_one_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1699_, 20, v_leFn_x3f_1664_);
lean_ctor_set(v_reuseFailAlloc_1699_, 21, v_ltFn_x3f_1665_);
lean_ctor_set(v_reuseFailAlloc_1699_, 22, v_addFn_1666_);
lean_ctor_set(v_reuseFailAlloc_1699_, 23, v_zsmulFn_1667_);
lean_ctor_set(v_reuseFailAlloc_1699_, 24, v_nsmulFn_1668_);
lean_ctor_set(v_reuseFailAlloc_1699_, 25, v_zsmulFn_x3f_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 26, v_nsmulFn_x3f_1670_);
lean_ctor_set(v_reuseFailAlloc_1699_, 27, v_homomulFn_x3f_1671_);
lean_ctor_set(v_reuseFailAlloc_1699_, 28, v_subFn_1672_);
lean_ctor_set(v_reuseFailAlloc_1699_, 29, v_negFn_1673_);
lean_ctor_set(v_reuseFailAlloc_1699_, 30, v_vars_1674_);
lean_ctor_set(v_reuseFailAlloc_1699_, 31, v_varMap_1675_);
lean_ctor_set(v_reuseFailAlloc_1699_, 32, v_lowers_1676_);
lean_ctor_set(v_reuseFailAlloc_1699_, 33, v_uppers_1677_);
lean_ctor_set(v_reuseFailAlloc_1699_, 34, v_diseqs_1678_);
lean_ctor_set(v_reuseFailAlloc_1699_, 35, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 36, v_conflict_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 37, v_diseqSplits_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 38, v_elimEqs_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 39, v_elimStack_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 40, v_occurs_1685_);
lean_ctor_set(v_reuseFailAlloc_1699_, 41, v_ignored_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*42, v_caseSplits_1680_);
v___x_1694_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_array_fset(v_xs_x27_1691_, v_a_1627_, v___x_1694_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1695_);
v___x_1697_ = v___x_1641_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_typeIdOf_1631_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_exprToStructId_1632_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_exprToStructIdEntries_1633_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_forbiddenNatModules_1634_);
lean_ctor_set(v_reuseFailAlloc_1698_, 5, v_natStructs_1635_);
lean_ctor_set(v_reuseFailAlloc_1698_, 6, v_natTypeIdOf_1636_);
lean_ctor_set(v_reuseFailAlloc_1698_, 7, v_exprToNatStructId_1637_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1710_, lean_object* v_x_1711_, lean_object* v_s_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1710_, v_x_1711_, v_s_1712_);
lean_dec(v_x_1711_);
lean_dec(v_a_1710_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_inc(v_a_1715_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1718_, 0, v_a_1715_);
lean_closure_set(v___f_1718_, 1, v_x_1714_);
v___x_1719_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1720_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1719_, v___f_1718_, v_a_1716_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1721_, v_a_1722_, v_a_1723_);
lean_dec(v_a_1723_);
lean_dec(v_a_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1726_, v_a_1727_, v_a_1728_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec(v_a_1741_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1784_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1784_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1784_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_vars_1772_; lean_object* v_size_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_vars_1772_ = lean_ctor_get(v_a_1768_, 30);
lean_inc_ref(v_vars_1772_);
lean_dec(v_a_1768_);
v_size_1773_ = lean_ctor_get(v_vars_1772_, 2);
v___x_1774_ = l_Lean_instInhabitedExpr;
v___x_1775_ = lean_nat_dec_lt(v_x_1754_, v_size_1773_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
lean_dec_ref(v_vars_1772_);
v___x_1776_ = l_outOfBounds___redArg(v___x_1774_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1776_);
v___x_1778_ = v___x_1770_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1774_, v_vars_1772_, v_x_1754_);
lean_dec_ref(v_vars_1772_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1780_);
v___x_1782_ = v___x_1770_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1785_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1767_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1767_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec(v_x_1793_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1808_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; uint8_t v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
v___x_1821_ = lean_unbox(v_a_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref_known(v___x_1819_, 1);
v___x_1822_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1836_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1836_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1836_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_conflict_x3f_1827_; 
v_conflict_x3f_1827_ = lean_ctor_get(v_a_1823_, 36);
lean_inc(v_conflict_x3f_1827_);
lean_dec(v_a_1823_);
if (lean_obj_tag(v_conflict_x3f_1827_) == 0)
{
lean_object* v___x_1829_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_a_1820_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1820_);
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
uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec_ref_known(v_conflict_x3f_1827_, 1);
lean_dec(v_a_1820_);
v___x_1831_ = 1;
v___x_1832_ = lean_box(v___x_1831_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1832_);
v___x_1834_ = v___x_1825_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_a_1820_);
v_a_1837_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1822_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1822_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_dec(v_a_1820_);
return v___x_1819_;
}
}
else
{
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
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
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1894_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1894_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1894_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___y_1877_; lean_object* v_elimEqs_1888_; lean_object* v_size_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_elimEqs_1888_ = lean_ctor_get(v_a_1872_, 38);
lean_inc_ref(v_elimEqs_1888_);
lean_dec(v_a_1872_);
v_size_1889_ = lean_ctor_get(v_elimEqs_1888_, 2);
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_nat_dec_lt(v_x_1858_, v_size_1889_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref(v_elimEqs_1888_);
v___x_1892_ = l_outOfBounds___redArg(v___x_1890_);
v___y_1877_ = v___x_1892_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1890_, v_elimEqs_1888_, v_x_1858_);
lean_dec_ref(v_elimEqs_1888_);
v___y_1877_ = v___x_1893_;
goto v___jp_1876_;
}
v___jp_1876_:
{
if (lean_obj_tag(v___y_1877_) == 0)
{
uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = 0;
v___x_1879_ = lean_box(v___x_1878_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1879_);
v___x_1881_ = v___x_1874_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
else
{
uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_dec_ref_known(v___y_1877_, 1);
v___x_1883_ = 1;
v___x_1884_ = lean_box(v___x_1883_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1884_);
v___x_1886_ = v___x_1874_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
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
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_a_1895_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1871_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1871_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_x_1903_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1947_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1947_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1947_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_occurs_1935_; lean_object* v_size_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_occurs_1935_ = lean_ctor_get(v_a_1931_, 40);
lean_inc_ref(v_occurs_1935_);
lean_dec(v_a_1931_);
v_size_1936_ = lean_ctor_get(v_occurs_1935_, 2);
v___x_1937_ = lean_box(1);
v___x_1938_ = lean_nat_dec_lt(v_x_1917_, v_size_1936_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec_ref(v_occurs_1935_);
v___x_1939_ = l_outOfBounds___redArg(v___x_1937_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1939_);
v___x_1941_ = v___x_1933_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1937_, v_occurs_1935_, v_x_1917_);
lean_dec_ref(v_occurs_1935_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1943_);
v___x_1945_ = v___x_1933_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1930_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1930_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec(v_x_1956_);
return v_res_1969_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1970_, lean_object* v_t_1971_){
_start:
{
if (lean_obj_tag(v_t_1971_) == 0)
{
lean_object* v_k_1972_; lean_object* v_l_1973_; lean_object* v_r_1974_; uint8_t v___x_1975_; 
v_k_1972_ = lean_ctor_get(v_t_1971_, 1);
v_l_1973_ = lean_ctor_get(v_t_1971_, 3);
v_r_1974_ = lean_ctor_get(v_t_1971_, 4);
v___x_1975_ = lean_nat_dec_lt(v_k_1970_, v_k_1972_);
if (v___x_1975_ == 0)
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_nat_dec_eq(v_k_1970_, v_k_1972_);
if (v___x_1976_ == 0)
{
v_t_1971_ = v_r_1974_;
goto _start;
}
else
{
return v___x_1976_;
}
}
else
{
v_t_1971_ = v_l_1973_;
goto _start;
}
}
else
{
uint8_t v___x_1979_; 
v___x_1979_ = 0;
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1980_, lean_object* v_t_1981_){
_start:
{
uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_res_1982_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1980_, v_t_1981_);
lean_dec(v_t_1981_);
lean_dec(v_k_1980_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1984_, lean_object* v_v_1985_, lean_object* v_t_1986_){
_start:
{
if (lean_obj_tag(v_t_1986_) == 0)
{
lean_object* v_size_1987_; lean_object* v_k_1988_; lean_object* v_v_1989_; lean_object* v_l_1990_; lean_object* v_r_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2272_; 
v_size_1987_ = lean_ctor_get(v_t_1986_, 0);
v_k_1988_ = lean_ctor_get(v_t_1986_, 1);
v_v_1989_ = lean_ctor_get(v_t_1986_, 2);
v_l_1990_ = lean_ctor_get(v_t_1986_, 3);
v_r_1991_ = lean_ctor_get(v_t_1986_, 4);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_t_1986_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_1993_ = v_t_1986_;
v_isShared_1994_ = v_isSharedCheck_2272_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_r_1991_);
lean_inc(v_l_1990_);
lean_inc(v_v_1989_);
lean_inc(v_k_1988_);
lean_inc(v_size_1987_);
lean_dec(v_t_1986_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2272_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_nat_dec_lt(v_k_1984_, v_k_1988_);
if (v___x_1995_ == 0)
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_eq(v_k_1984_, v_k_1988_);
if (v___x_1996_ == 0)
{
lean_object* v_impl_1997_; lean_object* v___x_1998_; 
lean_dec(v_size_1987_);
v_impl_1997_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1984_, v_v_1985_, v_r_1991_);
v___x_1998_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1990_) == 0)
{
lean_object* v_size_1999_; lean_object* v_size_2000_; lean_object* v_k_2001_; lean_object* v_v_2002_; lean_object* v_l_2003_; lean_object* v_r_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v_size_1999_ = lean_ctor_get(v_l_1990_, 0);
v_size_2000_ = lean_ctor_get(v_impl_1997_, 0);
lean_inc(v_size_2000_);
v_k_2001_ = lean_ctor_get(v_impl_1997_, 1);
lean_inc(v_k_2001_);
v_v_2002_ = lean_ctor_get(v_impl_1997_, 2);
lean_inc(v_v_2002_);
v_l_2003_ = lean_ctor_get(v_impl_1997_, 3);
lean_inc(v_l_2003_);
v_r_2004_ = lean_ctor_get(v_impl_1997_, 4);
lean_inc(v_r_2004_);
v___x_2005_ = lean_unsigned_to_nat(3u);
v___x_2006_ = lean_nat_mul(v___x_2005_, v_size_1999_);
v___x_2007_ = lean_nat_dec_lt(v___x_2006_, v_size_2000_);
lean_dec(v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_dec(v_r_2004_);
lean_dec(v_l_2003_);
lean_dec(v_v_2002_);
lean_dec(v_k_2001_);
v___x_2008_ = lean_nat_add(v___x_1998_, v_size_1999_);
v___x_2009_ = lean_nat_add(v___x_2008_, v_size_2000_);
lean_dec(v_size_2000_);
lean_dec(v___x_2008_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_impl_1997_);
lean_ctor_set(v___x_1993_, 0, v___x_2009_);
v___x_2011_ = v___x_1993_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_l_1990_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_impl_1997_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2076_; 
v_isSharedCheck_2076_ = !lean_is_exclusive(v_impl_1997_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2077_ = lean_ctor_get(v_impl_1997_, 4);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_impl_1997_, 3);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_1997_, 2);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_impl_1997_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_impl_1997_, 0);
lean_dec(v_unused_2081_);
v___x_2014_ = v_impl_1997_;
v_isShared_2015_ = v_isSharedCheck_2076_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_impl_1997_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2076_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_size_2016_; lean_object* v_k_2017_; lean_object* v_v_2018_; lean_object* v_l_2019_; lean_object* v_r_2020_; lean_object* v_size_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_size_2016_ = lean_ctor_get(v_l_2003_, 0);
v_k_2017_ = lean_ctor_get(v_l_2003_, 1);
v_v_2018_ = lean_ctor_get(v_l_2003_, 2);
v_l_2019_ = lean_ctor_get(v_l_2003_, 3);
v_r_2020_ = lean_ctor_get(v_l_2003_, 4);
v_size_2021_ = lean_ctor_get(v_r_2004_, 0);
v___x_2022_ = lean_unsigned_to_nat(2u);
v___x_2023_ = lean_nat_mul(v___x_2022_, v_size_2021_);
v___x_2024_ = lean_nat_dec_lt(v_size_2016_, v___x_2023_);
lean_dec(v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2052_; 
lean_inc(v_r_2020_);
lean_inc(v_l_2019_);
lean_inc(v_v_2018_);
lean_inc(v_k_2017_);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_l_2003_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2053_ = lean_ctor_get(v_l_2003_, 4);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_l_2003_, 3);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_l_2003_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_2003_, 1);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_l_2003_, 0);
lean_dec(v_unused_2057_);
v___x_2026_ = v_l_2003_;
v_isShared_2027_ = v_isSharedCheck_2052_;
goto v_resetjp_2025_;
}
else
{
lean_dec(v_l_2003_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2052_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2042_; 
v___x_2028_ = lean_nat_add(v___x_1998_, v_size_1999_);
v___x_2029_ = lean_nat_add(v___x_2028_, v_size_2000_);
lean_dec(v_size_2000_);
if (lean_obj_tag(v_l_2019_) == 0)
{
lean_object* v_size_2050_; 
v_size_2050_ = lean_ctor_get(v_l_2019_, 0);
lean_inc(v_size_2050_);
v___y_2042_ = v_size_2050_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___y_2042_ = v___x_2051_;
goto v___jp_2041_;
}
v___jp_2030_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_nat_add(v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec(v___y_2032_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_r_2004_);
lean_ctor_set(v___x_2026_, 3, v_r_2020_);
lean_ctor_set(v___x_2026_, 2, v_v_2002_);
lean_ctor_set(v___x_2026_, 1, v_k_2001_);
lean_ctor_set(v___x_2026_, 0, v___x_2034_);
v___x_2036_ = v___x_2026_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_2001_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_2002_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_r_2020_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_r_2004_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v___x_2036_);
lean_ctor_set(v___x_2014_, 3, v___y_2031_);
lean_ctor_set(v___x_2014_, 2, v_v_2018_);
lean_ctor_set(v___x_2014_, 1, v_k_2017_);
lean_ctor_set(v___x_2014_, 0, v___x_2029_);
v___x_2038_ = v___x_2014_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_k_2017_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_v_2018_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v___y_2031_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
v___jp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_nat_add(v___x_2028_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec(v___x_2028_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_l_2019_);
lean_ctor_set(v___x_1993_, 0, v___x_2043_);
v___x_2045_ = v___x_1993_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_l_1990_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_l_2019_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_nat_add(v___x_1998_, v_size_2021_);
if (lean_obj_tag(v_r_2020_) == 0)
{
lean_object* v_size_2047_; 
v_size_2047_ = lean_ctor_get(v_r_2020_, 0);
lean_inc(v_size_2047_);
v___y_2031_ = v___x_2045_;
v___y_2032_ = v___x_2046_;
v___y_2033_ = v_size_2047_;
goto v___jp_2030_;
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_unsigned_to_nat(0u);
v___y_2031_ = v___x_2045_;
v___y_2032_ = v___x_2046_;
v___y_2033_ = v___x_2048_;
goto v___jp_2030_;
}
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_del_object(v___x_1993_);
v___x_2058_ = lean_nat_add(v___x_1998_, v_size_1999_);
v___x_2059_ = lean_nat_add(v___x_2058_, v_size_2000_);
lean_dec(v_size_2000_);
v___x_2060_ = lean_nat_add(v___x_2058_, v_size_2016_);
lean_dec(v___x_2058_);
lean_inc_ref(v_l_1990_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v_l_2003_);
lean_ctor_set(v___x_2014_, 3, v_l_1990_);
lean_ctor_set(v___x_2014_, 2, v_v_1989_);
lean_ctor_set(v___x_2014_, 1, v_k_1988_);
lean_ctor_set(v___x_2014_, 0, v___x_2060_);
v___x_2062_ = v___x_2014_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_l_1990_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_l_2003_);
v___x_2062_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
v_isSharedCheck_2069_ = !lean_is_exclusive(v_l_1990_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; 
v_unused_2070_ = lean_ctor_get(v_l_1990_, 4);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_l_1990_, 3);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_l_1990_, 2);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_l_1990_, 1);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_l_1990_, 0);
lean_dec(v_unused_2074_);
v___x_2064_ = v_l_1990_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v_l_1990_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 4, v_r_2004_);
lean_ctor_set(v___x_2064_, 3, v___x_2062_);
lean_ctor_set(v___x_2064_, 2, v_v_2002_);
lean_ctor_set(v___x_2064_, 1, v_k_2001_);
lean_ctor_set(v___x_2064_, 0, v___x_2059_);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_2001_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_2002_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_r_2004_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2082_; 
v_l_2082_ = lean_ctor_get(v_impl_1997_, 3);
lean_inc(v_l_2082_);
if (lean_obj_tag(v_l_2082_) == 0)
{
lean_object* v_r_2083_; lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2108_; 
v_r_2083_ = lean_ctor_get(v_impl_1997_, 4);
v_k_2084_ = lean_ctor_get(v_impl_1997_, 1);
v_v_2085_ = lean_ctor_get(v_impl_1997_, 2);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_impl_1997_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; lean_object* v_unused_2110_; 
v_unused_2109_ = lean_ctor_get(v_impl_1997_, 3);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_impl_1997_, 0);
lean_dec(v_unused_2110_);
v___x_2087_ = v_impl_1997_;
v_isShared_2088_ = v_isSharedCheck_2108_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_r_2083_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_impl_1997_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2108_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_k_2089_; lean_object* v_v_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_k_2089_ = lean_ctor_get(v_l_2082_, 1);
v_v_2090_ = lean_ctor_get(v_l_2082_, 2);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_l_2082_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; lean_object* v_unused_2106_; lean_object* v_unused_2107_; 
v_unused_2105_ = lean_ctor_get(v_l_2082_, 4);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_2082_, 3);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_l_2082_, 0);
lean_dec(v_unused_2107_);
v___x_2092_ = v_l_2082_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
lean_dec(v_l_2082_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2083_, 2);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 4, v_r_2083_);
lean_ctor_set(v___x_2092_, 3, v_r_2083_);
lean_ctor_set(v___x_2092_, 2, v_v_1989_);
lean_ctor_set(v___x_2092_, 1, v_k_1988_);
lean_ctor_set(v___x_2092_, 0, v___x_1998_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_r_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_2083_);
v___x_2096_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
lean_inc(v_r_2083_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 3, v_r_2083_);
lean_ctor_set(v___x_2087_, 0, v___x_1998_);
v___x_2098_ = v___x_2087_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_r_2083_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_r_2083_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v___x_2098_);
lean_ctor_set(v___x_1993_, 3, v___x_2096_);
lean_ctor_set(v___x_1993_, 2, v_v_2090_);
lean_ctor_set(v___x_1993_, 1, v_k_2089_);
lean_ctor_set(v___x_1993_, 0, v___x_2094_);
v___x_2100_ = v___x_1993_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
else
{
lean_object* v_r_2111_; 
v_r_2111_ = lean_ctor_get(v_impl_1997_, 4);
lean_inc(v_r_2111_);
if (lean_obj_tag(v_r_2111_) == 0)
{
lean_object* v_k_2112_; lean_object* v_v_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2124_; 
v_k_2112_ = lean_ctor_get(v_impl_1997_, 1);
v_v_2113_ = lean_ctor_get(v_impl_1997_, 2);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_impl_1997_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; lean_object* v_unused_2126_; lean_object* v_unused_2127_; 
v_unused_2125_ = lean_ctor_get(v_impl_1997_, 4);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_impl_1997_, 3);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_impl_1997_, 0);
lean_dec(v_unused_2127_);
v___x_2115_ = v_impl_1997_;
v_isShared_2116_ = v_isSharedCheck_2124_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_v_2113_);
lean_inc(v_k_2112_);
lean_dec(v_impl_1997_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2124_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(3u);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 4, v_l_2082_);
lean_ctor_set(v___x_2115_, 2, v_v_1989_);
lean_ctor_set(v___x_2115_, 1, v_k_1988_);
lean_ctor_set(v___x_2115_, 0, v___x_1998_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_l_2082_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_l_2082_);
v___x_2119_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_r_2111_);
lean_ctor_set(v___x_1993_, 3, v___x_2119_);
lean_ctor_set(v___x_1993_, 2, v_v_2113_);
lean_ctor_set(v___x_1993_, 1, v_k_2112_);
lean_ctor_set(v___x_1993_, 0, v___x_2117_);
v___x_2121_ = v___x_1993_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_k_2112_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_v_2113_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_r_2111_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(2u);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_impl_1997_);
lean_ctor_set(v___x_1993_, 3, v_r_2111_);
lean_ctor_set(v___x_1993_, 0, v___x_2128_);
v___x_2130_ = v___x_1993_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_r_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v_impl_1997_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
else
{
lean_object* v___x_2133_; 
lean_dec(v_v_1989_);
lean_dec(v_k_1988_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 2, v_v_1985_);
lean_ctor_set(v___x_1993_, 1, v_k_1984_);
v___x_2133_ = v___x_1993_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_size_1987_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_1984_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_1985_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_l_1990_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_r_1991_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
lean_object* v_impl_2135_; lean_object* v___x_2136_; 
lean_dec(v_size_1987_);
v_impl_2135_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1984_, v_v_1985_, v_l_1990_);
v___x_2136_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1991_) == 0)
{
lean_object* v_size_2137_; lean_object* v_size_2138_; lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_l_2141_; lean_object* v_r_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_size_2137_ = lean_ctor_get(v_r_1991_, 0);
v_size_2138_ = lean_ctor_get(v_impl_2135_, 0);
lean_inc(v_size_2138_);
v_k_2139_ = lean_ctor_get(v_impl_2135_, 1);
lean_inc(v_k_2139_);
v_v_2140_ = lean_ctor_get(v_impl_2135_, 2);
lean_inc(v_v_2140_);
v_l_2141_ = lean_ctor_get(v_impl_2135_, 3);
lean_inc(v_l_2141_);
v_r_2142_ = lean_ctor_get(v_impl_2135_, 4);
lean_inc(v_r_2142_);
v___x_2143_ = lean_unsigned_to_nat(3u);
v___x_2144_ = lean_nat_mul(v___x_2143_, v_size_2137_);
v___x_2145_ = lean_nat_dec_lt(v___x_2144_, v_size_2138_);
lean_dec(v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec(v_r_2142_);
lean_dec(v_l_2141_);
lean_dec(v_v_2140_);
lean_dec(v_k_2139_);
v___x_2146_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2147_ = lean_nat_add(v___x_2146_, v_size_2137_);
lean_dec(v___x_2146_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 3, v_impl_2135_);
lean_ctor_set(v___x_1993_, 0, v___x_2147_);
v___x_2149_ = v___x_1993_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_impl_2135_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_r_1991_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
else
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2217_ = lean_ctor_get(v_impl_2135_, 4);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_impl_2135_, 2);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_impl_2135_, 1);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2221_);
v___x_2152_ = v_impl_2135_;
v_isShared_2153_ = v_isSharedCheck_2216_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v_impl_2135_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2216_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_size_2154_; lean_object* v_size_2155_; lean_object* v_k_2156_; lean_object* v_v_2157_; lean_object* v_l_2158_; lean_object* v_r_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_size_2154_ = lean_ctor_get(v_l_2141_, 0);
v_size_2155_ = lean_ctor_get(v_r_2142_, 0);
v_k_2156_ = lean_ctor_get(v_r_2142_, 1);
v_v_2157_ = lean_ctor_get(v_r_2142_, 2);
v_l_2158_ = lean_ctor_get(v_r_2142_, 3);
v_r_2159_ = lean_ctor_get(v_r_2142_, 4);
v___x_2160_ = lean_unsigned_to_nat(2u);
v___x_2161_ = lean_nat_mul(v___x_2160_, v_size_2154_);
v___x_2162_ = lean_nat_dec_lt(v_size_2155_, v___x_2161_);
lean_dec(v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2191_; 
lean_inc(v_r_2159_);
lean_inc(v_l_2158_);
lean_inc(v_v_2157_);
lean_inc(v_k_2156_);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_r_2142_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; 
v_unused_2192_ = lean_ctor_get(v_r_2142_, 4);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2142_, 3);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_2142_, 2);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_r_2142_, 1);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_r_2142_, 0);
lean_dec(v_unused_2196_);
v___x_2164_ = v_r_2142_;
v_isShared_2165_ = v_isSharedCheck_2191_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v_r_2142_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2191_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___x_2179_; lean_object* v___y_2181_; 
v___x_2166_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2167_ = lean_nat_add(v___x_2166_, v_size_2137_);
lean_dec(v___x_2166_);
v___x_2179_ = lean_nat_add(v___x_2136_, v_size_2154_);
if (lean_obj_tag(v_l_2158_) == 0)
{
lean_object* v_size_2189_; 
v_size_2189_ = lean_ctor_get(v_l_2158_, 0);
lean_inc(v_size_2189_);
v___y_2181_ = v_size_2189_;
goto v___jp_2180_;
}
else
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___y_2181_ = v___x_2190_;
goto v___jp_2180_;
}
v___jp_2168_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_nat_add(v___y_2169_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec(v___y_2169_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v_r_1991_);
lean_ctor_set(v___x_2164_, 3, v_r_2159_);
lean_ctor_set(v___x_2164_, 2, v_v_1989_);
lean_ctor_set(v___x_2164_, 1, v_k_1988_);
lean_ctor_set(v___x_2164_, 0, v___x_2172_);
v___x_2174_ = v___x_2164_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_r_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_r_1991_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v___x_2174_);
lean_ctor_set(v___x_2152_, 3, v___y_2170_);
lean_ctor_set(v___x_2152_, 2, v_v_2157_);
lean_ctor_set(v___x_2152_, 1, v_k_2156_);
lean_ctor_set(v___x_2152_, 0, v___x_2167_);
v___x_2176_ = v___x_2152_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___y_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
v___jp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_nat_add(v___x_2179_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec(v___x_2179_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_l_2158_);
lean_ctor_set(v___x_1993_, 3, v_l_2141_);
lean_ctor_set(v___x_1993_, 2, v_v_2140_);
lean_ctor_set(v___x_1993_, 1, v_k_2139_);
lean_ctor_set(v___x_1993_, 0, v___x_2182_);
v___x_2184_ = v___x_1993_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_l_2158_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_nat_add(v___x_2136_, v_size_2137_);
if (lean_obj_tag(v_r_2159_) == 0)
{
lean_object* v_size_2186_; 
v_size_2186_ = lean_ctor_get(v_r_2159_, 0);
lean_inc(v_size_2186_);
v___y_2169_ = v___x_2185_;
v___y_2170_ = v___x_2184_;
v___y_2171_ = v_size_2186_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___y_2169_ = v___x_2185_;
v___y_2170_ = v___x_2184_;
v___y_2171_ = v___x_2187_;
goto v___jp_2168_;
}
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_del_object(v___x_1993_);
v___x_2197_ = lean_nat_add(v___x_2136_, v_size_2138_);
lean_dec(v_size_2138_);
v___x_2198_ = lean_nat_add(v___x_2197_, v_size_2137_);
lean_dec(v___x_2197_);
v___x_2199_ = lean_nat_add(v___x_2136_, v_size_2137_);
v___x_2200_ = lean_nat_add(v___x_2199_, v_size_2155_);
lean_dec(v___x_2199_);
lean_inc_ref(v_r_1991_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v_r_1991_);
lean_ctor_set(v___x_2152_, 3, v_r_2142_);
lean_ctor_set(v___x_2152_, 2, v_v_1989_);
lean_ctor_set(v___x_2152_, 1, v_k_1988_);
lean_ctor_set(v___x_2152_, 0, v___x_2200_);
v___x_2202_ = v___x_2152_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_r_2142_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_r_1991_);
v___x_2202_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v_r_1991_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2210_ = lean_ctor_get(v_r_1991_, 4);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_r_1991_, 3);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_r_1991_, 2);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_r_1991_, 1);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_r_1991_, 0);
lean_dec(v_unused_2214_);
v___x_2204_ = v_r_1991_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v_r_1991_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 4, v___x_2202_);
lean_ctor_set(v___x_2204_, 3, v_l_2141_);
lean_ctor_set(v___x_2204_, 2, v_v_2140_);
lean_ctor_set(v___x_2204_, 1, v_k_2139_);
lean_ctor_set(v___x_2204_, 0, v___x_2198_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v___x_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2222_; 
v_l_2222_ = lean_ctor_get(v_impl_2135_, 3);
lean_inc(v_l_2222_);
if (lean_obj_tag(v_l_2222_) == 0)
{
lean_object* v_r_2223_; lean_object* v_k_2224_; lean_object* v_v_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2236_; 
v_r_2223_ = lean_ctor_get(v_impl_2135_, 4);
v_k_2224_ = lean_ctor_get(v_impl_2135_, 1);
v_v_2225_ = lean_ctor_get(v_impl_2135_, 2);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; lean_object* v_unused_2238_; 
v_unused_2237_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2238_);
v___x_2227_ = v_impl_2135_;
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_r_2223_);
lean_inc(v_v_2225_);
lean_inc(v_k_2224_);
lean_dec(v_impl_2135_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2223_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 3, v_r_2223_);
lean_ctor_set(v___x_2227_, 2, v_v_1989_);
lean_ctor_set(v___x_2227_, 1, v_k_1988_);
lean_ctor_set(v___x_2227_, 0, v___x_2136_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_r_2223_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_r_2223_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v___x_2231_);
lean_ctor_set(v___x_1993_, 3, v_l_2222_);
lean_ctor_set(v___x_1993_, 2, v_v_2225_);
lean_ctor_set(v___x_1993_, 1, v_k_2224_);
lean_ctor_set(v___x_1993_, 0, v___x_2229_);
v___x_2233_ = v___x_1993_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v___x_2231_);
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
else
{
lean_object* v_r_2239_; 
v_r_2239_ = lean_ctor_get(v_impl_2135_, 4);
lean_inc(v_r_2239_);
if (lean_obj_tag(v_r_2239_) == 0)
{
lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2264_; 
v_k_2240_ = lean_ctor_get(v_impl_2135_, 1);
v_v_2241_ = lean_ctor_get(v_impl_2135_, 2);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_impl_2135_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; lean_object* v_unused_2266_; lean_object* v_unused_2267_; 
v_unused_2265_ = lean_ctor_get(v_impl_2135_, 4);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_impl_2135_, 3);
lean_dec(v_unused_2266_);
v_unused_2267_ = lean_ctor_get(v_impl_2135_, 0);
lean_dec(v_unused_2267_);
v___x_2243_ = v_impl_2135_;
v_isShared_2244_ = v_isSharedCheck_2264_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_dec(v_impl_2135_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2264_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_k_2245_; lean_object* v_v_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2260_; 
v_k_2245_ = lean_ctor_get(v_r_2239_, 1);
v_v_2246_ = lean_ctor_get(v_r_2239_, 2);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_r_2239_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2261_ = lean_ctor_get(v_r_2239_, 4);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_r_2239_, 3);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_r_2239_, 0);
lean_dec(v_unused_2263_);
v___x_2248_ = v_r_2239_;
v_isShared_2249_ = v_isSharedCheck_2260_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_v_2246_);
lean_inc(v_k_2245_);
lean_dec(v_r_2239_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2260_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(3u);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v_l_2222_);
lean_ctor_set(v___x_2248_, 3, v_l_2222_);
lean_ctor_set(v___x_2248_, 2, v_v_2241_);
lean_ctor_set(v___x_2248_, 1, v_k_2240_);
lean_ctor_set(v___x_2248_, 0, v___x_2136_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v_l_2222_);
v___x_2252_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2254_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 4, v_l_2222_);
lean_ctor_set(v___x_2243_, 2, v_v_1989_);
lean_ctor_set(v___x_2243_, 1, v_k_1988_);
lean_ctor_set(v___x_2243_, 0, v___x_2136_);
v___x_2254_ = v___x_2243_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_l_2222_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_l_2222_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v___x_2254_);
lean_ctor_set(v___x_1993_, 3, v___x_2252_);
lean_ctor_set(v___x_1993_, 2, v_v_2246_);
lean_ctor_set(v___x_1993_, 1, v_k_2245_);
lean_ctor_set(v___x_1993_, 0, v___x_2250_);
v___x_2256_ = v___x_1993_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_k_2245_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_v_2246_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_unsigned_to_nat(2u);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v_r_2239_);
lean_ctor_set(v___x_1993_, 3, v_impl_2135_);
lean_ctor_set(v___x_1993_, 0, v___x_2268_);
v___x_2270_ = v___x_1993_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_impl_2135_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_r_2239_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(1u);
v___x_2274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v_k_1984_);
lean_ctor_set(v___x_2274_, 2, v_v_1985_);
lean_ctor_set(v___x_2274_, 3, v_t_1986_);
lean_ctor_set(v___x_2274_, 4, v_t_1986_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2275_, lean_object* v_x_2276_, size_t v_x_2277_, size_t v_x_2278_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v_cs_2279_; size_t v_j_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_cs_2279_ = lean_ctor_get(v_x_2276_, 0);
v_j_2280_ = lean_usize_shift_right(v_x_2277_, v_x_2278_);
v___x_2281_ = lean_usize_to_nat(v_j_2280_);
v___x_2282_ = lean_array_get_size(v_cs_2279_);
v___x_2283_ = lean_nat_dec_lt(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_dec(v___x_2281_);
lean_dec(v_y_2275_);
return v_x_2276_;
}
else
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2301_; 
lean_inc_ref(v_cs_2279_);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v_x_2276_, 0);
lean_dec(v_unused_2302_);
v___x_2285_ = v_x_2276_;
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_x_2276_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
size_t v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; size_t v_i_2290_; size_t v___x_2291_; size_t v_shift_2292_; lean_object* v_v_2293_; lean_object* v___x_2294_; lean_object* v_xs_x27_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2287_ = ((size_t)1ULL);
v___x_2288_ = lean_usize_shift_left(v___x_2287_, v_x_2278_);
v___x_2289_ = lean_usize_sub(v___x_2288_, v___x_2287_);
v_i_2290_ = lean_usize_land(v_x_2277_, v___x_2289_);
v___x_2291_ = ((size_t)5ULL);
v_shift_2292_ = lean_usize_sub(v_x_2278_, v___x_2291_);
v_v_2293_ = lean_array_fget(v_cs_2279_, v___x_2281_);
v___x_2294_ = lean_box(0);
v_xs_x27_2295_ = lean_array_fset(v_cs_2279_, v___x_2281_, v___x_2294_);
v___x_2296_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2275_, v_v_2293_, v_i_2290_, v_shift_2292_);
v___x_2297_ = lean_array_fset(v_xs_x27_2295_, v___x_2281_, v___x_2296_);
lean_dec(v___x_2281_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2297_);
v___x_2299_ = v___x_2285_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_vs_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_vs_2303_ = lean_ctor_get(v_x_2276_, 0);
v___x_2304_ = lean_usize_to_nat(v_x_2277_);
v___x_2305_ = lean_array_get_size(v_vs_2303_);
v___x_2306_ = lean_nat_dec_lt(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec(v___x_2304_);
lean_dec(v_y_2275_);
return v_x_2276_;
}
else
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2321_; 
lean_inc_ref(v_vs_2303_);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_x_2276_, 0);
lean_dec(v_unused_2322_);
v___x_2308_ = v_x_2276_;
v_isShared_2309_ = v_isSharedCheck_2321_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v_x_2276_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2321_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_v_2310_; lean_object* v___x_2311_; lean_object* v_xs_x27_2312_; lean_object* v___y_2314_; uint8_t v___x_2319_; 
v_v_2310_ = lean_array_fget(v_vs_2303_, v___x_2304_);
v___x_2311_ = lean_box(0);
v_xs_x27_2312_ = lean_array_fset(v_vs_2303_, v___x_2304_, v___x_2311_);
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2275_, v_v_2310_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2275_, v___x_2311_, v_v_2310_);
v___y_2314_ = v___x_2320_;
goto v___jp_2313_;
}
else
{
lean_dec(v_y_2275_);
v___y_2314_ = v_v_2310_;
goto v___jp_2313_;
}
v___jp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_array_fset(v_xs_x27_2312_, v___x_2304_, v___y_2314_);
lean_dec(v___x_2304_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2315_);
v___x_2317_ = v___x_2308_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
size_t v_x_6038__boxed_2327_; size_t v_x_6039__boxed_2328_; lean_object* v_res_2329_; 
v_x_6038__boxed_2327_ = lean_unbox_usize(v_x_2325_);
lean_dec(v_x_2325_);
v_x_6039__boxed_2328_ = lean_unbox_usize(v_x_2326_);
lean_dec(v_x_2326_);
v_res_2329_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2323_, v_x_2324_, v_x_6038__boxed_2327_, v_x_6039__boxed_2328_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2330_, lean_object* v_t_2331_, lean_object* v_i_2332_){
_start:
{
lean_object* v_root_2333_; lean_object* v_tail_2334_; lean_object* v_size_2335_; size_t v_shift_2336_; lean_object* v_tailOff_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2364_; 
v_root_2333_ = lean_ctor_get(v_t_2331_, 0);
v_tail_2334_ = lean_ctor_get(v_t_2331_, 1);
v_size_2335_ = lean_ctor_get(v_t_2331_, 2);
v_shift_2336_ = lean_ctor_get_usize(v_t_2331_, 4);
v_tailOff_2337_ = lean_ctor_get(v_t_2331_, 3);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_t_2331_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2339_ = v_t_2331_;
v_isShared_2340_ = v_isSharedCheck_2364_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_tailOff_2337_);
lean_inc(v_size_2335_);
lean_inc(v_tail_2334_);
lean_inc(v_root_2333_);
lean_dec(v_t_2331_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2364_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_le(v_tailOff_2337_, v_i_2332_);
if (v___x_2341_ == 0)
{
size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = lean_usize_of_nat(v_i_2332_);
v___x_2343_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2330_, v_root_2333_, v___x_2342_, v_shift_2336_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2343_);
v___x_2345_ = v___x_2339_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_tail_2334_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_size_2335_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_tailOff_2337_);
lean_ctor_set_usize(v_reuseFailAlloc_2346_, 4, v_shift_2336_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2347_ = lean_nat_sub(v_i_2332_, v_tailOff_2337_);
v___x_2348_ = lean_array_get_size(v_tail_2334_);
v___x_2349_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2351_; 
lean_dec(v___x_2347_);
lean_dec(v_y_2330_);
if (v_isShared_2340_ == 0)
{
v___x_2351_ = v___x_2339_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_root_2333_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_tail_2334_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_size_2335_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_tailOff_2337_);
lean_ctor_set_usize(v_reuseFailAlloc_2352_, 4, v_shift_2336_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
lean_object* v_v_2353_; lean_object* v___x_2354_; lean_object* v_xs_x27_2355_; lean_object* v___y_2357_; uint8_t v___x_2362_; 
v_v_2353_ = lean_array_fget(v_tail_2334_, v___x_2347_);
v___x_2354_ = lean_box(0);
v_xs_x27_2355_ = lean_array_fset(v_tail_2334_, v___x_2347_, v___x_2354_);
v___x_2362_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2330_, v_v_2353_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2330_, v___x_2354_, v_v_2353_);
v___y_2357_ = v___x_2363_;
goto v___jp_2356_;
}
else
{
lean_dec(v_y_2330_);
v___y_2357_ = v_v_2353_;
goto v___jp_2356_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_array_fset(v_xs_x27_2355_, v___x_2347_, v___y_2357_);
lean_dec(v___x_2347_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v___x_2358_);
v___x_2360_ = v___x_2339_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_root_2333_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_size_2335_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v_tailOff_2337_);
lean_ctor_set_usize(v_reuseFailAlloc_2361_, 4, v_shift_2336_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2365_, lean_object* v_t_2366_, lean_object* v_i_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2365_, v_t_2366_, v_i_2367_);
lean_dec(v_i_2367_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2369_, lean_object* v_y_2370_, lean_object* v_x_2371_, lean_object* v_s_2372_){
_start:
{
lean_object* v_structs_2373_; lean_object* v_typeIdOf_2374_; lean_object* v_exprToStructId_2375_; lean_object* v_exprToStructIdEntries_2376_; lean_object* v_forbiddenNatModules_2377_; lean_object* v_natStructs_2378_; lean_object* v_natTypeIdOf_2379_; lean_object* v_exprToNatStructId_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_structs_2373_ = lean_ctor_get(v_s_2372_, 0);
v_typeIdOf_2374_ = lean_ctor_get(v_s_2372_, 1);
v_exprToStructId_2375_ = lean_ctor_get(v_s_2372_, 2);
v_exprToStructIdEntries_2376_ = lean_ctor_get(v_s_2372_, 3);
v_forbiddenNatModules_2377_ = lean_ctor_get(v_s_2372_, 4);
v_natStructs_2378_ = lean_ctor_get(v_s_2372_, 5);
v_natTypeIdOf_2379_ = lean_ctor_get(v_s_2372_, 6);
v_exprToNatStructId_2380_ = lean_ctor_get(v_s_2372_, 7);
v___x_2381_ = lean_array_get_size(v_structs_2373_);
v___x_2382_ = lean_nat_dec_lt(v_a_2369_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec(v_y_2370_);
return v_s_2372_;
}
else
{
lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2444_; 
lean_inc_ref(v_exprToNatStructId_2380_);
lean_inc_ref(v_natTypeIdOf_2379_);
lean_inc_ref(v_natStructs_2378_);
lean_inc_ref(v_forbiddenNatModules_2377_);
lean_inc_ref(v_exprToStructIdEntries_2376_);
lean_inc_ref(v_exprToStructId_2375_);
lean_inc_ref(v_typeIdOf_2374_);
lean_inc_ref(v_structs_2373_);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_s_2372_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; lean_object* v_unused_2450_; lean_object* v_unused_2451_; lean_object* v_unused_2452_; 
v_unused_2445_ = lean_ctor_get(v_s_2372_, 7);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_s_2372_, 6);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_s_2372_, 5);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_s_2372_, 4);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_s_2372_, 3);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_s_2372_, 2);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_s_2372_, 1);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_s_2372_, 0);
lean_dec(v_unused_2452_);
v___x_2384_ = v_s_2372_;
v_isShared_2385_ = v_isSharedCheck_2444_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v_s_2372_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2444_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_v_2386_; lean_object* v_id_2387_; lean_object* v_ringId_x3f_2388_; lean_object* v_type_2389_; lean_object* v_u_2390_; lean_object* v_intModuleInst_2391_; lean_object* v_leInst_x3f_2392_; lean_object* v_ltInst_x3f_2393_; lean_object* v_lawfulOrderLTInst_x3f_2394_; lean_object* v_isPreorderInst_x3f_2395_; lean_object* v_orderedAddInst_x3f_2396_; lean_object* v_isLinearInst_x3f_2397_; lean_object* v_noNatDivInst_x3f_2398_; lean_object* v_ringInst_x3f_2399_; lean_object* v_commRingInst_x3f_2400_; lean_object* v_orderedRingInst_x3f_2401_; lean_object* v_fieldInst_x3f_2402_; lean_object* v_charInst_x3f_2403_; lean_object* v_zero_2404_; lean_object* v_ofNatZero_2405_; lean_object* v_one_x3f_2406_; lean_object* v_leFn_x3f_2407_; lean_object* v_ltFn_x3f_2408_; lean_object* v_addFn_2409_; lean_object* v_zsmulFn_2410_; lean_object* v_nsmulFn_2411_; lean_object* v_zsmulFn_x3f_2412_; lean_object* v_nsmulFn_x3f_2413_; lean_object* v_homomulFn_x3f_2414_; lean_object* v_subFn_2415_; lean_object* v_negFn_2416_; lean_object* v_vars_2417_; lean_object* v_varMap_2418_; lean_object* v_lowers_2419_; lean_object* v_uppers_2420_; lean_object* v_diseqs_2421_; lean_object* v_assignment_2422_; uint8_t v_caseSplits_2423_; lean_object* v_conflict_x3f_2424_; lean_object* v_diseqSplits_2425_; lean_object* v_elimEqs_2426_; lean_object* v_elimStack_2427_; lean_object* v_occurs_2428_; lean_object* v_ignored_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2443_; 
v_v_2386_ = lean_array_fget(v_structs_2373_, v_a_2369_);
v_id_2387_ = lean_ctor_get(v_v_2386_, 0);
v_ringId_x3f_2388_ = lean_ctor_get(v_v_2386_, 1);
v_type_2389_ = lean_ctor_get(v_v_2386_, 2);
v_u_2390_ = lean_ctor_get(v_v_2386_, 3);
v_intModuleInst_2391_ = lean_ctor_get(v_v_2386_, 4);
v_leInst_x3f_2392_ = lean_ctor_get(v_v_2386_, 5);
v_ltInst_x3f_2393_ = lean_ctor_get(v_v_2386_, 6);
v_lawfulOrderLTInst_x3f_2394_ = lean_ctor_get(v_v_2386_, 7);
v_isPreorderInst_x3f_2395_ = lean_ctor_get(v_v_2386_, 8);
v_orderedAddInst_x3f_2396_ = lean_ctor_get(v_v_2386_, 9);
v_isLinearInst_x3f_2397_ = lean_ctor_get(v_v_2386_, 10);
v_noNatDivInst_x3f_2398_ = lean_ctor_get(v_v_2386_, 11);
v_ringInst_x3f_2399_ = lean_ctor_get(v_v_2386_, 12);
v_commRingInst_x3f_2400_ = lean_ctor_get(v_v_2386_, 13);
v_orderedRingInst_x3f_2401_ = lean_ctor_get(v_v_2386_, 14);
v_fieldInst_x3f_2402_ = lean_ctor_get(v_v_2386_, 15);
v_charInst_x3f_2403_ = lean_ctor_get(v_v_2386_, 16);
v_zero_2404_ = lean_ctor_get(v_v_2386_, 17);
v_ofNatZero_2405_ = lean_ctor_get(v_v_2386_, 18);
v_one_x3f_2406_ = lean_ctor_get(v_v_2386_, 19);
v_leFn_x3f_2407_ = lean_ctor_get(v_v_2386_, 20);
v_ltFn_x3f_2408_ = lean_ctor_get(v_v_2386_, 21);
v_addFn_2409_ = lean_ctor_get(v_v_2386_, 22);
v_zsmulFn_2410_ = lean_ctor_get(v_v_2386_, 23);
v_nsmulFn_2411_ = lean_ctor_get(v_v_2386_, 24);
v_zsmulFn_x3f_2412_ = lean_ctor_get(v_v_2386_, 25);
v_nsmulFn_x3f_2413_ = lean_ctor_get(v_v_2386_, 26);
v_homomulFn_x3f_2414_ = lean_ctor_get(v_v_2386_, 27);
v_subFn_2415_ = lean_ctor_get(v_v_2386_, 28);
v_negFn_2416_ = lean_ctor_get(v_v_2386_, 29);
v_vars_2417_ = lean_ctor_get(v_v_2386_, 30);
v_varMap_2418_ = lean_ctor_get(v_v_2386_, 31);
v_lowers_2419_ = lean_ctor_get(v_v_2386_, 32);
v_uppers_2420_ = lean_ctor_get(v_v_2386_, 33);
v_diseqs_2421_ = lean_ctor_get(v_v_2386_, 34);
v_assignment_2422_ = lean_ctor_get(v_v_2386_, 35);
v_caseSplits_2423_ = lean_ctor_get_uint8(v_v_2386_, sizeof(void*)*42);
v_conflict_x3f_2424_ = lean_ctor_get(v_v_2386_, 36);
v_diseqSplits_2425_ = lean_ctor_get(v_v_2386_, 37);
v_elimEqs_2426_ = lean_ctor_get(v_v_2386_, 38);
v_elimStack_2427_ = lean_ctor_get(v_v_2386_, 39);
v_occurs_2428_ = lean_ctor_get(v_v_2386_, 40);
v_ignored_2429_ = lean_ctor_get(v_v_2386_, 41);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_v_2386_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2431_ = v_v_2386_;
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_ignored_2429_);
lean_inc(v_occurs_2428_);
lean_inc(v_elimStack_2427_);
lean_inc(v_elimEqs_2426_);
lean_inc(v_diseqSplits_2425_);
lean_inc(v_conflict_x3f_2424_);
lean_inc(v_assignment_2422_);
lean_inc(v_diseqs_2421_);
lean_inc(v_uppers_2420_);
lean_inc(v_lowers_2419_);
lean_inc(v_varMap_2418_);
lean_inc(v_vars_2417_);
lean_inc(v_negFn_2416_);
lean_inc(v_subFn_2415_);
lean_inc(v_homomulFn_x3f_2414_);
lean_inc(v_nsmulFn_x3f_2413_);
lean_inc(v_zsmulFn_x3f_2412_);
lean_inc(v_nsmulFn_2411_);
lean_inc(v_zsmulFn_2410_);
lean_inc(v_addFn_2409_);
lean_inc(v_ltFn_x3f_2408_);
lean_inc(v_leFn_x3f_2407_);
lean_inc(v_one_x3f_2406_);
lean_inc(v_ofNatZero_2405_);
lean_inc(v_zero_2404_);
lean_inc(v_charInst_x3f_2403_);
lean_inc(v_fieldInst_x3f_2402_);
lean_inc(v_orderedRingInst_x3f_2401_);
lean_inc(v_commRingInst_x3f_2400_);
lean_inc(v_ringInst_x3f_2399_);
lean_inc(v_noNatDivInst_x3f_2398_);
lean_inc(v_isLinearInst_x3f_2397_);
lean_inc(v_orderedAddInst_x3f_2396_);
lean_inc(v_isPreorderInst_x3f_2395_);
lean_inc(v_lawfulOrderLTInst_x3f_2394_);
lean_inc(v_ltInst_x3f_2393_);
lean_inc(v_leInst_x3f_2392_);
lean_inc(v_intModuleInst_2391_);
lean_inc(v_u_2390_);
lean_inc(v_type_2389_);
lean_inc(v_ringId_x3f_2388_);
lean_inc(v_id_2387_);
lean_dec(v_v_2386_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2443_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v_xs_x27_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2433_ = lean_box(0);
v_xs_x27_2434_ = lean_array_fset(v_structs_2373_, v_a_2369_, v___x_2433_);
v___x_2435_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2370_, v_occurs_2428_, v_x_2371_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 40, v___x_2435_);
v___x_2437_ = v___x_2431_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_id_2387_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_ringId_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_type_2389_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v_u_2390_);
lean_ctor_set(v_reuseFailAlloc_2442_, 4, v_intModuleInst_2391_);
lean_ctor_set(v_reuseFailAlloc_2442_, 5, v_leInst_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2442_, 6, v_ltInst_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2442_, 7, v_lawfulOrderLTInst_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2442_, 8, v_isPreorderInst_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2442_, 9, v_orderedAddInst_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2442_, 10, v_isLinearInst_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2442_, 11, v_noNatDivInst_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2442_, 12, v_ringInst_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2442_, 13, v_commRingInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2442_, 14, v_orderedRingInst_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2442_, 15, v_fieldInst_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2442_, 16, v_charInst_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2442_, 17, v_zero_2404_);
lean_ctor_set(v_reuseFailAlloc_2442_, 18, v_ofNatZero_2405_);
lean_ctor_set(v_reuseFailAlloc_2442_, 19, v_one_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2442_, 20, v_leFn_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2442_, 21, v_ltFn_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2442_, 22, v_addFn_2409_);
lean_ctor_set(v_reuseFailAlloc_2442_, 23, v_zsmulFn_2410_);
lean_ctor_set(v_reuseFailAlloc_2442_, 24, v_nsmulFn_2411_);
lean_ctor_set(v_reuseFailAlloc_2442_, 25, v_zsmulFn_x3f_2412_);
lean_ctor_set(v_reuseFailAlloc_2442_, 26, v_nsmulFn_x3f_2413_);
lean_ctor_set(v_reuseFailAlloc_2442_, 27, v_homomulFn_x3f_2414_);
lean_ctor_set(v_reuseFailAlloc_2442_, 28, v_subFn_2415_);
lean_ctor_set(v_reuseFailAlloc_2442_, 29, v_negFn_2416_);
lean_ctor_set(v_reuseFailAlloc_2442_, 30, v_vars_2417_);
lean_ctor_set(v_reuseFailAlloc_2442_, 31, v_varMap_2418_);
lean_ctor_set(v_reuseFailAlloc_2442_, 32, v_lowers_2419_);
lean_ctor_set(v_reuseFailAlloc_2442_, 33, v_uppers_2420_);
lean_ctor_set(v_reuseFailAlloc_2442_, 34, v_diseqs_2421_);
lean_ctor_set(v_reuseFailAlloc_2442_, 35, v_assignment_2422_);
lean_ctor_set(v_reuseFailAlloc_2442_, 36, v_conflict_x3f_2424_);
lean_ctor_set(v_reuseFailAlloc_2442_, 37, v_diseqSplits_2425_);
lean_ctor_set(v_reuseFailAlloc_2442_, 38, v_elimEqs_2426_);
lean_ctor_set(v_reuseFailAlloc_2442_, 39, v_elimStack_2427_);
lean_ctor_set(v_reuseFailAlloc_2442_, 40, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 41, v_ignored_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2442_, sizeof(void*)*42, v_caseSplits_2423_);
v___x_2437_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_array_fset(v_xs_x27_2434_, v_a_2369_, v___x_2437_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2438_);
v___x_2440_ = v___x_2384_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_typeIdOf_2374_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_exprToStructId_2375_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_exprToStructIdEntries_2376_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_forbiddenNatModules_2377_);
lean_ctor_set(v_reuseFailAlloc_2441_, 5, v_natStructs_2378_);
lean_ctor_set(v_reuseFailAlloc_2441_, 6, v_natTypeIdOf_2379_);
lean_ctor_set(v_reuseFailAlloc_2441_, 7, v_exprToNatStructId_2380_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2453_, lean_object* v_y_2454_, lean_object* v_x_2455_, lean_object* v_s_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2453_, v_y_2454_, v_x_2455_, v_s_2456_);
lean_dec(v_x_2455_);
lean_dec(v_a_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2458_, lean_object* v_y_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2458_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2485_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2485_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
uint8_t v___x_2477_; 
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2459_, v_a_2473_);
lean_dec(v_a_2473_);
if (v___x_2477_ == 0)
{
lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_del_object(v___x_2475_);
lean_inc(v_a_2460_);
v___f_2478_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2478_, 0, v_a_2460_);
lean_closure_set(v___f_2478_, 1, v_y_2459_);
lean_closure_set(v___f_2478_, 2, v_x_2458_);
v___x_2479_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2480_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2479_, v___f_2478_, v_a_2461_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_dec(v_y_2459_);
lean_dec(v_x_2458_);
v___x_2481_ = lean_box(0);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2481_);
v___x_2483_ = v___x_2475_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_y_2459_);
lean_dec(v_x_2458_);
v_a_2486_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2472_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2472_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2494_, lean_object* v_y_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2494_, v_y_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec(v_a_2496_);
return v_res_2508_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2509_, lean_object* v_k_2510_, lean_object* v_t_2511_){
_start:
{
uint8_t v___x_2512_; 
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2510_, v_t_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2513_, lean_object* v_k_2514_, lean_object* v_t_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2513_, v_k_2514_, v_t_2515_);
lean_dec(v_t_2515_);
lean_dec(v_k_2514_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2518_, lean_object* v_k_2519_, lean_object* v_v_2520_, lean_object* v_t_2521_, lean_object* v_hl_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2519_, v_v_2520_, v_t_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2524_, lean_object* v_p_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
if (lean_obj_tag(v_p_2525_) == 1)
{
lean_object* v_v_2538_; lean_object* v_p_2539_; lean_object* v___x_2540_; 
v_v_2538_ = lean_ctor_get(v_p_2525_, 1);
lean_inc(v_v_2538_);
v_p_2539_ = lean_ctor_get(v_p_2525_, 2);
lean_inc(v_p_2539_);
lean_dec_ref_known(v_p_2525_, 3);
lean_inc(v_y_2524_);
v___x_2540_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2538_, v_y_2524_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
v_p_2525_ = v_p_2539_;
goto _start;
}
else
{
lean_dec(v_p_2539_);
lean_dec(v_y_2524_);
return v___x_2540_;
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v_p_2525_);
lean_dec(v_y_2524_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2544_, lean_object* v_p_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2544_, v_p_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2558_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
if (lean_obj_tag(v_p_2562_) == 1)
{
lean_object* v_v_2575_; lean_object* v_p_2576_; lean_object* v___x_2577_; 
v_v_2575_ = lean_ctor_get(v_p_2562_, 1);
lean_inc(v_v_2575_);
v_p_2576_ = lean_ctor_get(v_p_2562_, 2);
lean_inc(v_p_2576_);
lean_dec_ref_known(v_p_2562_, 3);
v___x_2577_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2575_, v_p_2576_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_p_2562_);
v___x_2578_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2579_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2578_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec(v_a_2581_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
if (lean_obj_tag(v_p_2594_) == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
else
{
lean_object* v_k_2609_; lean_object* v_v_2610_; lean_object* v_p_2611_; lean_object* v___x_2612_; 
v_k_2609_ = lean_ctor_get(v_p_2594_, 0);
v_v_2610_ = lean_ctor_get(v_p_2594_, 1);
v_p_2611_ = lean_ctor_get(v_p_2594_, 2);
v___x_2612_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2639_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2639_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2639_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___y_2618_; lean_object* v_elimEqs_2633_; lean_object* v_size_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_elimEqs_2633_ = lean_ctor_get(v_a_2613_, 38);
lean_inc_ref(v_elimEqs_2633_);
lean_dec(v_a_2613_);
v_size_2634_ = lean_ctor_get(v_elimEqs_2633_, 2);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_nat_dec_lt(v_v_2610_, v_size_2634_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; 
lean_dec_ref(v_elimEqs_2633_);
v___x_2637_ = l_outOfBounds___redArg(v___x_2635_);
v___y_2618_ = v___x_2637_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2635_, v_elimEqs_2633_, v_v_2610_);
lean_dec_ref(v_elimEqs_2633_);
v___y_2618_ = v___x_2638_;
goto v___jp_2617_;
}
v___jp_2617_:
{
if (lean_obj_tag(v___y_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2631_; 
v_val_2619_ = lean_ctor_get(v___y_2618_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___y_2618_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2621_ = v___y_2618_;
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v___y_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2631_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_inc(v_v_2610_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_v_2610_);
lean_ctor_set(v___x_2623_, 1, v_val_2619_);
lean_inc(v_k_2609_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_k_2609_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2624_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2626_);
v___x_2628_ = v___x_2615_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
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
else
{
lean_dec(v___y_2618_);
lean_del_object(v___x_2615_);
v_p_2594_ = v_p_2611_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2612_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2612_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_p_2648_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
return v_x_2663_;
}
else
{
lean_object* v_k_2664_; lean_object* v_p_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_k_2664_ = lean_ctor_get(v_x_2662_, 0);
v_p_2665_ = lean_ctor_get(v_x_2662_, 2);
v___x_2666_ = lean_nat_to_int(v_x_2663_);
v___x_2667_ = l_Int_gcd(v_k_2664_, v___x_2666_);
lean_dec(v___x_2666_);
v_x_2662_ = v_p_2665_;
v_x_2663_ = v___x_2667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2669_, lean_object* v_x_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2669_, v_x_2670_);
lean_dec(v_x_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2672_){
_start:
{
if (lean_obj_tag(v_p_2672_) == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_unsigned_to_nat(1u);
return v___x_2673_;
}
else
{
lean_object* v_k_2674_; lean_object* v_p_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_k_2674_ = lean_ctor_get(v_p_2672_, 0);
v_p_2675_ = lean_ctor_get(v_p_2672_, 2);
v___x_2676_ = lean_nat_abs(v_k_2674_);
v___x_2677_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2675_, v___x_2676_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2678_);
lean_dec(v_p_2678_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2680_, lean_object* v_k_2681_){
_start:
{
if (lean_obj_tag(v_p_2680_) == 0)
{
return v_p_2680_;
}
else
{
lean_object* v_k_2682_; lean_object* v_v_2683_; lean_object* v_p_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2693_; 
v_k_2682_ = lean_ctor_get(v_p_2680_, 0);
v_v_2683_ = lean_ctor_get(v_p_2680_, 1);
v_p_2684_ = lean_ctor_get(v_p_2680_, 2);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_p_2680_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2686_ = v_p_2680_;
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_p_2684_);
lean_inc(v_v_2683_);
lean_inc(v_k_2682_);
lean_dec(v_p_2680_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = lean_int_ediv(v_k_2682_, v_k_2681_);
lean_dec(v_k_2682_);
v___x_2689_ = l_Lean_Grind_Linarith_Poly_div(v_p_2684_, v_k_2681_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 2, v___x_2689_);
lean_ctor_set(v___x_2686_, 0, v___x_2688_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_v_2683_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2694_, lean_object* v_k_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Grind_Linarith_Poly_div(v_p_2694_, v_k_2695_);
lean_dec(v_k_2695_);
return v_res_2696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_to_int(v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2700_ = lean_int_neg(v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2701_, lean_object* v_x_2702_, lean_object* v_p_2703_){
_start:
{
uint8_t v___y_2705_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v___x_2716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2717_ = lean_int_dec_eq(v_k_2701_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2719_ = lean_int_dec_eq(v_k_2701_, v___x_2718_);
v___y_2705_ = v___x_2719_;
goto v___jp_2704_;
}
else
{
v___y_2705_ = v___x_2717_;
goto v___jp_2704_;
}
v___jp_2704_:
{
if (v___y_2705_ == 0)
{
if (lean_obj_tag(v_p_2703_) == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_k_2701_);
lean_ctor_set(v___x_2706_, 1, v_x_2702_);
return v___x_2706_;
}
else
{
lean_object* v_k_2707_; lean_object* v_v_2708_; lean_object* v_p_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_k_2707_ = lean_ctor_get(v_p_2703_, 0);
lean_inc(v_k_2707_);
v_v_2708_ = lean_ctor_get(v_p_2703_, 1);
lean_inc(v_v_2708_);
v_p_2709_ = lean_ctor_get(v_p_2703_, 2);
lean_inc(v_p_2709_);
lean_dec_ref_known(v_p_2703_, 3);
v___x_2710_ = lean_nat_abs(v_k_2707_);
v___x_2711_ = lean_nat_abs(v_k_2701_);
v___x_2712_ = lean_nat_dec_lt(v___x_2710_, v___x_2711_);
lean_dec(v___x_2711_);
lean_dec(v___x_2710_);
if (v___x_2712_ == 0)
{
lean_dec(v_v_2708_);
lean_dec(v_k_2707_);
v_p_2703_ = v_p_2709_;
goto _start;
}
else
{
lean_dec(v_x_2702_);
lean_dec(v_k_2701_);
v_k_2701_ = v_k_2707_;
v_x_2702_ = v_v_2708_;
v_p_2703_ = v_p_2709_;
goto _start;
}
}
}
else
{
lean_object* v___x_2715_; 
lean_dec(v_p_2703_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_k_2701_);
lean_ctor_set(v___x_2715_, 1, v_x_2702_);
return v___x_2715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2720_){
_start:
{
if (lean_obj_tag(v_p_2720_) == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_box(0);
return v___x_2721_;
}
else
{
lean_object* v_k_2722_; lean_object* v_v_2723_; lean_object* v_p_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_k_2722_ = lean_ctor_get(v_p_2720_, 0);
lean_inc(v_k_2722_);
v_v_2723_ = lean_ctor_get(v_p_2720_, 1);
lean_inc(v_v_2723_);
v_p_2724_ = lean_ctor_get(v_p_2720_, 2);
lean_inc(v_p_2724_);
lean_dec_ref_known(v_p_2720_, 3);
v___x_2725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2722_, v_v_2723_, v_p_2724_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
