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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "expression in two different structure in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_one_x3f_61_);
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
lean_dec_ref(v_ringId_x3f_106_);
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
lean_dec_ref(v___x_151_);
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
lean_dec_ref(v_orderedRingInst_x3f_167_);
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
lean_dec_ref(v_isLinearInst_x3f_215_);
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
lean_dec_ref(v_noNatDivInst_x3f_265_);
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
lean_object* v_k_x27_305_; uint8_t v___x_306_; 
v_k_x27_305_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v___x_306_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_301_, v_k_x27_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_300_, v___x_307_);
lean_dec(v_i_300_);
v_i_300_ = v___x_308_;
goto _start;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
lean_dec(v_i_300_);
lean_inc(v___x_310_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_312_, lean_object* v_vals_313_, lean_object* v_i_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_312_, v_vals_313_, v_i_314_, v_k_315_);
lean_dec_ref(v_k_315_);
lean_dec_ref(v_vals_313_);
lean_dec_ref(v_keys_312_);
return v_res_316_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; 
v___x_317_ = ((size_t)5ULL);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_shift_left(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; 
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_322_ = lean_usize_sub(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_323_, size_t v_x_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_es_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_347_; 
v_es_326_ = lean_ctor_get(v_x_323_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_347_ == 0)
{
v___x_328_ = v_x_323_;
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_es_326_);
lean_dec(v_x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_j_334_; lean_object* v___x_335_; 
v___x_330_ = lean_box(2);
v___x_331_ = ((size_t)5ULL);
v___x_332_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_333_ = lean_usize_land(v_x_324_, v___x_332_);
v_j_334_ = lean_usize_to_nat(v___x_333_);
v___x_335_ = lean_array_get(v___x_330_, v_es_326_, v_j_334_);
lean_dec(v_j_334_);
lean_dec_ref(v_es_326_);
switch(lean_obj_tag(v___x_335_))
{
case 0:
{
lean_object* v_key_336_; lean_object* v_val_337_; uint8_t v___x_338_; 
v_key_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_key_336_);
v_val_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_val_337_);
lean_dec_ref(v___x_335_);
v___x_338_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_325_, v_key_336_);
lean_dec(v_key_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v_val_337_);
lean_del_object(v___x_328_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_341_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
lean_ctor_set(v___x_328_, 0, v_val_337_);
v___x_341_ = v___x_328_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_val_337_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
case 1:
{
lean_object* v_node_343_; size_t v___x_344_; 
lean_del_object(v___x_328_);
v_node_343_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_node_343_);
lean_dec_ref(v___x_335_);
v___x_344_ = lean_usize_shift_right(v_x_324_, v___x_331_);
v_x_323_ = v_node_343_;
v_x_324_ = v___x_344_;
goto _start;
}
default: 
{
lean_object* v___x_346_; 
lean_del_object(v___x_328_);
v___x_346_ = lean_box(0);
return v___x_346_;
}
}
}
}
else
{
lean_object* v_ks_348_; lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_ks_348_ = lean_ctor_get(v_x_323_, 0);
lean_inc_ref(v_ks_348_);
v_vs_349_ = lean_ctor_get(v_x_323_, 1);
lean_inc_ref(v_vs_349_);
lean_dec_ref(v_x_323_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_348_, v_vs_349_, v___x_350_, v_x_325_);
lean_dec_ref(v_vs_349_);
lean_dec_ref(v_ks_348_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
size_t v_x_867__boxed_355_; lean_object* v_res_356_; 
v_x_867__boxed_355_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_352_, v_x_867__boxed_355_, v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint64_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_359_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_358_);
v___x_360_ = lean_uint64_to_usize(v___x_359_);
v___x_361_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_357_, v___x_360_, v_x_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_362_, v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_exprToStructId_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v_exprToStructId_374_ = lean_ctor_get(v_a_370_, 2);
lean_inc_ref(v_exprToStructId_374_);
lean_dec(v_a_370_);
v___x_375_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_374_, v_e_365_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_369_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_388_, v_a_389_, v_a_390_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_e_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_393_, v_a_394_, v_a_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_e_406_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_423_, v_x_424_, v_x_425_);
lean_dec_ref(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, size_t v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_428_, v_x_429_, v_x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
size_t v_x_996__boxed_436_; lean_object* v_res_437_; 
v_x_996__boxed_436_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_432_, v_x_433_, v_x_996__boxed_436_, v_x_435_);
lean_dec_ref(v_x_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_438_, lean_object* v_keys_439_, lean_object* v_vals_440_, lean_object* v_heq_441_, lean_object* v_i_442_, lean_object* v_k_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_439_, v_vals_440_, v_i_442_, v_k_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_445_, lean_object* v_keys_446_, lean_object* v_vals_447_, lean_object* v_heq_448_, lean_object* v_i_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_445_, v_keys_446_, v_vals_447_, v_heq_448_, v_i_449_, v_k_450_);
lean_dec_ref(v_k_450_);
lean_dec_ref(v_vals_447_);
lean_dec_ref(v_keys_446_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_ks_456_; lean_object* v_vs_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_481_; 
v_ks_456_ = lean_ctor_get(v_x_452_, 0);
v_vs_457_ = lean_ctor_get(v_x_452_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_481_ == 0)
{
v___x_459_ = v_x_452_;
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_vs_457_);
lean_inc(v_ks_456_);
lean_dec(v_x_452_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_array_get_size(v_ks_456_);
v___x_462_ = lean_nat_dec_lt(v_x_453_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v_x_453_);
v___x_463_ = lean_array_push(v_ks_456_, v_x_454_);
v___x_464_ = lean_array_push(v_vs_457_, v_x_455_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_464_);
lean_ctor_set(v___x_459_, 0, v___x_463_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v_k_x27_468_; uint8_t v___x_469_; 
v_k_x27_468_ = lean_array_fget_borrowed(v_ks_456_, v_x_453_);
v___x_469_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_454_, v_k_x27_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; 
if (v_isShared_460_ == 0)
{
v___x_471_ = v___x_459_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_ks_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_vs_457_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_x_453_, v___x_472_);
lean_dec(v_x_453_);
v_x_452_ = v___x_471_;
v_x_453_ = v___x_473_;
goto _start;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_array_fset(v_ks_456_, v_x_453_, v_x_454_);
v___x_477_ = lean_array_fset(v_vs_457_, v_x_453_, v_x_455_);
lean_dec(v_x_453_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_477_);
lean_ctor_set(v___x_459_, 0, v___x_476_);
v___x_479_ = v___x_459_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_482_, lean_object* v_k_483_, lean_object* v_v_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_482_, v___x_485_, v_k_483_, v_v_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_488_, size_t v_x_489_, size_t v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v_es_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v_j_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_es_493_ = lean_ctor_get(v_x_488_, 0);
v___x_494_ = ((size_t)5ULL);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_497_ = lean_usize_land(v_x_489_, v___x_496_);
v_j_498_ = lean_usize_to_nat(v___x_497_);
v___x_499_ = lean_array_get_size(v_es_493_);
v___x_500_ = lean_nat_dec_lt(v_j_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v_j_498_);
lean_dec(v_x_492_);
lean_dec_ref(v_x_491_);
return v_x_488_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_537_; 
lean_inc_ref(v_es_493_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v_x_488_, 0);
lean_dec(v_unused_538_);
v___x_502_ = v_x_488_;
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_x_488_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_v_504_; lean_object* v___x_505_; lean_object* v_xs_x27_506_; lean_object* v___y_508_; 
v_v_504_ = lean_array_fget(v_es_493_, v_j_498_);
v___x_505_ = lean_box(0);
v_xs_x27_506_ = lean_array_fset(v_es_493_, v_j_498_, v___x_505_);
switch(lean_obj_tag(v_v_504_))
{
case 0:
{
lean_object* v_key_513_; lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
v_key_513_ = lean_ctor_get(v_v_504_, 0);
v_val_514_ = lean_ctor_get(v_v_504_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_524_ == 0)
{
v___x_516_ = v_v_504_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_inc(v_key_513_);
lean_dec(v_v_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_491_, v_key_513_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_516_);
v___x_519_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_513_, v_val_514_, v_x_491_, v_x_492_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___y_508_ = v___x_520_;
goto v___jp_507_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_val_514_);
lean_dec(v_key_513_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_x_492_);
lean_ctor_set(v___x_516_, 0, v_x_491_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_x_491_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_x_492_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v___y_508_ = v___x_522_;
goto v___jp_507_;
}
}
}
}
case 1:
{
lean_object* v_node_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
v_node_525_ = lean_ctor_get(v_v_504_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_535_ == 0)
{
v___x_527_ = v_v_504_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_node_525_);
lean_dec(v_v_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_529_ = lean_usize_shift_right(v_x_489_, v___x_494_);
v___x_530_ = lean_usize_add(v_x_490_, v___x_495_);
v___x_531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_525_, v___x_529_, v___x_530_, v_x_491_, v_x_492_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_531_);
v___x_533_ = v___x_527_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_508_ = v___x_533_;
goto v___jp_507_;
}
}
}
default: 
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_x_491_);
lean_ctor_set(v___x_536_, 1, v_x_492_);
v___y_508_ = v___x_536_;
goto v___jp_507_;
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_fset(v_xs_x27_506_, v_j_498_, v___y_508_);
lean_dec(v_j_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_509_);
v___x_511_ = v___x_502_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
else
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_560_; 
v_ks_539_ = lean_ctor_get(v_x_488_, 0);
v_vs_540_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_560_ == 0)
{
v___x_542_ = v_x_488_;
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_488_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vs_540_);
v___x_545_ = v_reuseFailAlloc_559_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v_newNode_546_; uint8_t v___y_548_; size_t v___x_554_; uint8_t v___x_555_; 
v_newNode_546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_545_, v_x_491_, v_x_492_);
v___x_554_ = ((size_t)7ULL);
v___x_555_ = lean_usize_dec_le(v___x_554_, v_x_490_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_546_);
v___x_557_ = lean_unsigned_to_nat(4u);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v___y_548_ = v___x_558_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___x_555_;
goto v___jp_547_;
}
v___jp_547_:
{
if (v___y_548_ == 0)
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_ks_549_ = lean_ctor_get(v_newNode_546_, 0);
lean_inc_ref(v_ks_549_);
v_vs_550_ = lean_ctor_get(v_newNode_546_, 1);
lean_inc_ref(v_vs_550_);
lean_dec_ref(v_newNode_546_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_553_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_490_, v_ks_549_, v_vs_550_, v___x_551_, v___x_552_);
lean_dec_ref(v_vs_550_);
lean_dec_ref(v_ks_549_);
return v___x_553_;
}
else
{
return v_newNode_546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_561_, lean_object* v_keys_562_, lean_object* v_vals_563_, lean_object* v_i_564_, lean_object* v_entries_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_keys_562_);
v___x_567_ = lean_nat_dec_lt(v_i_564_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_i_564_);
return v_entries_565_;
}
else
{
lean_object* v_k_568_; lean_object* v_v_569_; uint64_t v___x_570_; size_t v_h_571_; size_t v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v_h_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_k_568_ = lean_array_fget_borrowed(v_keys_562_, v_i_564_);
v_v_569_ = lean_array_fget_borrowed(v_vals_563_, v_i_564_);
v___x_570_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_568_);
v_h_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v_depth_561_, v___x_574_);
v___x_576_ = lean_usize_mul(v___x_572_, v___x_575_);
v_h_577_ = lean_usize_shift_right(v_h_571_, v___x_576_);
v___x_578_ = lean_nat_add(v_i_564_, v___x_573_);
lean_dec(v_i_564_);
lean_inc(v_v_569_);
lean_inc(v_k_568_);
v___x_579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_565_, v_h_577_, v_depth_561_, v_k_568_, v_v_569_);
v_i_564_ = v___x_578_;
v_entries_565_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_i_584_, lean_object* v_entries_585_){
_start:
{
size_t v_depth_boxed_586_; lean_object* v_res_587_; 
v_depth_boxed_586_ = lean_unbox_usize(v_depth_581_);
lean_dec(v_depth_581_);
v_res_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_586_, v_keys_582_, v_vals_583_, v_i_584_, v_entries_585_);
lean_dec_ref(v_vals_583_);
lean_dec_ref(v_keys_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_8335__boxed_593_; size_t v_x_8336__boxed_594_; lean_object* v_res_595_; 
v_x_8335__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_x_8336__boxed_594_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_588_, v_x_8335__boxed_593_, v_x_8336__boxed_594_, v_x_591_, v_x_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_599_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_597_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_596_, v___x_600_, v___x_601_, v_x_597_, v_x_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_s_605_){
_start:
{
lean_object* v_structs_606_; lean_object* v_typeIdOf_607_; lean_object* v_exprToStructId_608_; lean_object* v_exprToStructIdEntries_609_; lean_object* v_forbiddenNatModules_610_; lean_object* v_natStructs_611_; lean_object* v_natTypeIdOf_612_; lean_object* v_exprToNatStructId_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
v_structs_606_ = lean_ctor_get(v_s_605_, 0);
v_typeIdOf_607_ = lean_ctor_get(v_s_605_, 1);
v_exprToStructId_608_ = lean_ctor_get(v_s_605_, 2);
v_exprToStructIdEntries_609_ = lean_ctor_get(v_s_605_, 3);
v_forbiddenNatModules_610_ = lean_ctor_get(v_s_605_, 4);
v_natStructs_611_ = lean_ctor_get(v_s_605_, 5);
v_natTypeIdOf_612_ = lean_ctor_get(v_s_605_, 6);
v_exprToNatStructId_613_ = lean_ctor_get(v_s_605_, 7);
v_isSharedCheck_623_ = !lean_is_exclusive(v_s_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_615_ = v_s_605_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_exprToNatStructId_613_);
lean_inc(v_natTypeIdOf_612_);
lean_inc(v_natStructs_611_);
lean_inc(v_forbiddenNatModules_610_);
lean_inc(v_exprToStructIdEntries_609_);
lean_inc(v_exprToStructId_608_);
lean_inc(v_typeIdOf_607_);
lean_inc(v_structs_606_);
lean_dec(v_s_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_inc(v_a_604_);
lean_inc_ref(v_e_603_);
v___x_617_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_608_, v_e_603_, v_a_604_);
lean_inc(v_a_604_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_e_603_);
lean_ctor_set(v___x_618_, 1, v_a_604_);
v___x_619_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_609_, v___x_618_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 3, v___x_619_);
lean_ctor_set(v___x_615_, 2, v___x_617_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_structs_606_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_typeIdOf_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_forbiddenNatModules_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_natStructs_611_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_natTypeIdOf_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_exprToNatStructId_613_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0___boxed(lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_s_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0(v_e_624_, v_a_625_, v_s_626_);
lean_dec(v_a_625_);
return v_res_627_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_631_, v_a_633_, v_a_641_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
if (lean_obj_tag(v_a_648_) == 1)
{
lean_object* v_val_649_; uint8_t v___x_650_; 
v_val_649_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v_a_648_);
v___x_650_ = lean_nat_dec_eq(v_val_649_, v_a_632_);
lean_dec(v_val_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_635_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v_verbose_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v_verbose_653_ = lean_ctor_get_uint8(v_a_652_, sizeof(void*)*11 + 15);
lean_dec(v_a_652_);
if (v_verbose_653_ == 0)
{
lean_dec_ref(v_e_631_);
goto v___jp_644_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1);
v___x_655_ = l_Lean_indentExpr(v_e_631_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_Meta_Grind_reportIssue(v___x_656_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
goto v___jp_644_;
}
else
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_e_631_);
v_a_658_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_651_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_651_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_dec_ref(v_e_631_);
goto v___jp_644_;
}
}
else
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_a_648_);
lean_inc(v_a_632_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_666_, 0, v_e_631_);
lean_closure_set(v___f_666_, 1, v_a_632_);
v___x_667_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_667_, v___f_666_, v_a_633_);
return v___x_668_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_e_631_);
v_a_669_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_647_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_647_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec(v_a_679_);
lean_dec(v_a_678_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_692_, v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, size_t v_x_698_, size_t v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_697_, v_x_698_, v_x_699_, v_x_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
size_t v_x_8611__boxed_709_; size_t v_x_8612__boxed_710_; lean_object* v_res_711_; 
v_x_8611__boxed_709_ = lean_unbox_usize(v_x_705_);
lean_dec(v_x_705_);
v_x_8612__boxed_710_ = lean_unbox_usize(v_x_706_);
lean_dec(v_x_706_);
v_res_711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_703_, v_x_704_, v_x_8611__boxed_709_, v_x_8612__boxed_710_, v_x_707_, v_x_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_712_, lean_object* v_n_713_, lean_object* v_k_714_, lean_object* v_v_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_713_, v_k_714_, v_v_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_717_, size_t v_depth_718_, lean_object* v_keys_719_, lean_object* v_vals_720_, lean_object* v_heq_721_, lean_object* v_i_722_, lean_object* v_entries_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_718_, v_keys_719_, v_vals_720_, v_i_722_, v_entries_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_725_, lean_object* v_depth_726_, lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_heq_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
size_t v_depth_boxed_732_; lean_object* v_res_733_; 
v_depth_boxed_732_ = lean_unbox_usize(v_depth_726_);
lean_dec(v_depth_726_);
v_res_733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_725_, v_depth_boxed_732_, v_keys_727_, v_vals_728_, v_heq_729_, v_i_730_, v_entries_731_);
lean_dec_ref(v_vals_728_);
lean_dec_ref(v_keys_727_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_735_, v_x_736_, v_x_737_, v_x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; lean_object* v_env_747_; lean_object* v___x_748_; lean_object* v_mctx_749_; lean_object* v_lctx_750_; lean_object* v_options_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_746_ = lean_st_ref_get(v___y_744_);
v_env_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc_ref(v_env_747_);
lean_dec(v___x_746_);
v___x_748_ = lean_st_ref_get(v___y_742_);
v_mctx_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc_ref(v_mctx_749_);
lean_dec(v___x_748_);
v_lctx_750_ = lean_ctor_get(v___y_741_, 2);
v_options_751_ = lean_ctor_get(v___y_743_, 2);
lean_inc_ref(v_options_751_);
lean_inc_ref(v_lctx_750_);
v___x_752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_752_, 0, v_env_747_);
lean_ctor_set(v___x_752_, 1, v_mctx_749_);
lean_ctor_set(v___x_752_, 2, v_lctx_750_);
lean_ctor_set(v___x_752_, 3, v_options_751_);
v___x_753_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_msgData_740_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_ref_768_; lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
v_ref_768_ = lean_ctor_get(v___y_765_, 5);
v___x_769_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_778_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_inc(v_ref_768_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_ref_768_);
lean_ctor_set(v___x_774_, 1, v_a_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 1);
lean_ctor_set(v___x_772_, 0, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_813_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_813_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_813_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_noNatDivInst_x3f_806_; 
v_noNatDivInst_x3f_806_ = lean_ctor_get(v_a_802_, 11);
lean_inc(v_noNatDivInst_x3f_806_);
lean_dec(v_a_802_);
if (lean_obj_tag(v_noNatDivInst_x3f_806_) == 1)
{
lean_object* v_val_807_; lean_object* v___x_809_; 
v_val_807_ = lean_ctor_get(v_noNatDivInst_x3f_806_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v_noNatDivInst_x3f_806_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_val_807_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_noNatDivInst_x3f_806_);
lean_del_object(v___x_804_);
v___x_811_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_812_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_811_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_812_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_a_814_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_801_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_801_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec(v_a_823_);
lean_dec(v_a_822_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_835_, lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_836_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_850_, lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_850_, v_msg_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
return v_res_864_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_892_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_leInst_x3f_885_; 
v_leInst_x3f_885_ = lean_ctor_get(v_a_881_, 5);
lean_inc(v_leInst_x3f_885_);
lean_dec(v_a_881_);
if (lean_obj_tag(v_leInst_x3f_885_) == 1)
{
lean_object* v_val_886_; lean_object* v___x_888_; 
v_val_886_ = lean_ctor_get(v_leInst_x3f_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref(v_leInst_x3f_885_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_val_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_val_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_leInst_x3f_885_);
lean_del_object(v___x_883_);
v___x_890_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_891_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_890_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
return v___x_891_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_880_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_880_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_941_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_941_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_941_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_941_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_ltInst_x3f_934_; 
v_ltInst_x3f_934_ = lean_ctor_get(v_a_930_, 6);
lean_inc(v_ltInst_x3f_934_);
lean_dec(v_a_930_);
if (lean_obj_tag(v_ltInst_x3f_934_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_937_; 
v_val_935_ = lean_ctor_get(v_ltInst_x3f_934_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v_ltInst_x3f_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v_val_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_val_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_ltInst_x3f_934_);
lean_del_object(v___x_932_);
v___x_939_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_940_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_939_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
return v___x_940_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_929_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_929_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_990_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_lawfulOrderLTInst_x3f_983_; 
v_lawfulOrderLTInst_x3f_983_ = lean_ctor_get(v_a_979_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_983_);
lean_dec(v_a_979_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; 
v_val_984_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_983_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_val_984_);
v___x_986_ = v___x_981_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_val_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_lawfulOrderLTInst_x3f_983_);
lean_del_object(v___x_981_);
v___x_988_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_989_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_988_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_989_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_978_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_978_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec(v_a_999_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1039_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1039_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_isPreorderInst_x3f_1032_; 
v_isPreorderInst_x3f_1032_ = lean_ctor_get(v_a_1028_, 8);
lean_inc(v_isPreorderInst_x3f_1032_);
lean_dec(v_a_1028_);
if (lean_obj_tag(v_isPreorderInst_x3f_1032_) == 1)
{
lean_object* v_val_1033_; lean_object* v___x_1035_; 
v_val_1033_ = lean_ctor_get(v_isPreorderInst_x3f_1032_, 0);
lean_inc(v_val_1033_);
lean_dec_ref(v_isPreorderInst_x3f_1032_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_val_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_val_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_isPreorderInst_x3f_1032_);
lean_del_object(v___x_1030_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1038_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1037_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1027_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1027_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1088_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_orderedAddInst_x3f_1081_; 
v_orderedAddInst_x3f_1081_ = lean_ctor_get(v_a_1077_, 9);
lean_inc(v_orderedAddInst_x3f_1081_);
lean_dec(v_a_1077_);
if (lean_obj_tag(v_orderedAddInst_x3f_1081_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1084_; 
v_val_1082_ = lean_ctor_get(v_orderedAddInst_x3f_1081_, 0);
lean_inc(v_val_1082_);
lean_dec_ref(v_orderedAddInst_x3f_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_val_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_val_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_orderedAddInst_x3f_1081_);
lean_del_object(v___x_1079_);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1087_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1086_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1076_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1076_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1138_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1138_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_orderedAddInst_x3f_1127_; 
v_orderedAddInst_x3f_1127_ = lean_ctor_get(v_a_1123_, 9);
lean_inc(v_orderedAddInst_x3f_1127_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v_orderedAddInst_x3f_1127_) == 0)
{
uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1128_ = 0;
v___x_1129_ = lean_box(v___x_1128_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1129_);
v___x_1131_ = v___x_1125_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec_ref(v_orderedAddInst_x3f_1127_);
v___x_1133_ = 1;
v___x_1134_ = lean_box(v___x_1133_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1134_);
v___x_1136_ = v___x_1125_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1122_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1122_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec(v_a_1147_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_____do__lift_1163_){
_start:
{
lean_object* v_ltFn_x3f_1164_; 
v_ltFn_x3f_1164_ = lean_ctor_get(v_____do__lift_1163_, 21);
lean_inc(v_ltFn_x3f_1164_);
lean_dec_ref(v_____do__lift_1163_);
if (lean_obj_tag(v_ltFn_x3f_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_inst_1162_);
lean_dec_ref(v_inst_1161_);
v_val_1165_ = lean_ctor_get(v_ltFn_x3f_1164_, 0);
lean_inc(v_val_1165_);
lean_dec_ref(v_ltFn_x3f_1164_);
v___x_1166_ = lean_apply_2(v_toPure_1160_, lean_box(0), v_val_1165_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_ltFn_x3f_1164_);
lean_dec(v_toPure_1160_);
v___x_1167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1168_ = l_Lean_throwError___redArg(v_inst_1161_, v_inst_1162_, v___x_1167_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_){
_start:
{
lean_object* v_toApplicative_1172_; lean_object* v_toBind_1173_; lean_object* v_toPure_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v_toApplicative_1172_ = lean_ctor_get(v_inst_1169_, 0);
v_toBind_1173_ = lean_ctor_get(v_inst_1169_, 1);
lean_inc(v_toBind_1173_);
v_toPure_1174_ = lean_ctor_get(v_toApplicative_1172_, 1);
lean_inc(v_toPure_1174_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1175_, 0, v_toPure_1174_);
lean_closure_set(v___f_1175_, 1, v_inst_1169_);
lean_closure_set(v___f_1175_, 2, v_inst_1170_);
v___x_1176_ = lean_apply_4(v_toBind_1173_, lean_box(0), lean_box(0), v_inst_1171_, v___f_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1178_, v_inst_1179_, v_inst_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1184_ = l_Lean_stringToMessageData(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_____do__lift_1188_){
_start:
{
lean_object* v_leFn_x3f_1189_; 
v_leFn_x3f_1189_ = lean_ctor_get(v_____do__lift_1188_, 20);
lean_inc(v_leFn_x3f_1189_);
lean_dec_ref(v_____do__lift_1188_);
if (lean_obj_tag(v_leFn_x3f_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v_val_1190_ = lean_ctor_get(v_leFn_x3f_1189_, 0);
lean_inc(v_val_1190_);
lean_dec_ref(v_leFn_x3f_1189_);
v___x_1191_ = lean_apply_2(v_toPure_1185_, lean_box(0), v_val_1190_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec(v_leFn_x3f_1189_);
lean_dec(v_toPure_1185_);
v___x_1192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1193_ = l_Lean_throwError___redArg(v_inst_1186_, v_inst_1187_, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_){
_start:
{
lean_object* v_toApplicative_1197_; lean_object* v_toBind_1198_; lean_object* v_toPure_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; 
v_toApplicative_1197_ = lean_ctor_get(v_inst_1194_, 0);
v_toBind_1198_ = lean_ctor_get(v_inst_1194_, 1);
lean_inc(v_toBind_1198_);
v_toPure_1199_ = lean_ctor_get(v_toApplicative_1197_, 1);
lean_inc(v_toPure_1199_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1200_, 0, v_toPure_1199_);
lean_closure_set(v___f_1200_, 1, v_inst_1194_);
lean_closure_set(v___f_1200_, 2, v_inst_1195_);
v___x_1201_ = lean_apply_4(v_toBind_1198_, lean_box(0), lean_box(0), v_inst_1196_, v___f_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1203_, v_inst_1204_, v_inst_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_isLinearInst_x3f_1227_; 
v_isLinearInst_x3f_1227_ = lean_ctor_get(v_a_1223_, 10);
lean_inc(v_isLinearInst_x3f_1227_);
lean_dec(v_a_1223_);
if (lean_obj_tag(v_isLinearInst_x3f_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v___x_1230_; 
v_val_1228_ = lean_ctor_get(v_isLinearInst_x3f_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref(v_isLinearInst_x3f_1227_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_val_1228_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_val_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_isLinearInst_x3f_1227_);
lean_del_object(v___x_1225_);
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1233_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1232_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1235_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1222_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1222_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec(v_a_1243_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1283_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_ringInst_x3f_1276_; 
v_ringInst_x3f_1276_ = lean_ctor_get(v_a_1272_, 12);
lean_inc(v_ringInst_x3f_1276_);
lean_dec(v_a_1272_);
if (lean_obj_tag(v_ringInst_x3f_1276_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1279_; 
v_val_1277_ = lean_ctor_get(v_ringInst_x3f_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v_ringInst_x3f_1276_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_val_1277_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_val_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_ringInst_x3f_1276_);
lean_del_object(v___x_1274_);
v___x_1281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1282_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1281_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1271_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1271_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec(v_a_1292_);
return v_res_1304_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1332_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_commRingInst_x3f_1325_; 
v_commRingInst_x3f_1325_ = lean_ctor_get(v_a_1321_, 13);
lean_inc(v_commRingInst_x3f_1325_);
lean_dec(v_a_1321_);
if (lean_obj_tag(v_commRingInst_x3f_1325_) == 1)
{
lean_object* v_val_1326_; lean_object* v___x_1328_; 
v_val_1326_ = lean_ctor_get(v_commRingInst_x3f_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref(v_commRingInst_x3f_1325_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_val_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_val_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_commRingInst_x3f_1325_);
lean_del_object(v___x_1323_);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1331_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1330_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1320_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1320_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec(v_a_1341_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1381_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_orderedRingInst_x3f_1374_; 
v_orderedRingInst_x3f_1374_ = lean_ctor_get(v_a_1370_, 14);
lean_inc(v_orderedRingInst_x3f_1374_);
lean_dec(v_a_1370_);
if (lean_obj_tag(v_orderedRingInst_x3f_1374_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1377_; 
v_val_1375_ = lean_ctor_get(v_orderedRingInst_x3f_1374_, 0);
lean_inc(v_val_1375_);
lean_dec_ref(v_orderedRingInst_x3f_1374_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_val_1375_);
v___x_1377_ = v___x_1372_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_orderedRingInst_x3f_1374_);
lean_del_object(v___x_1372_);
v___x_1379_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1380_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1379_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1380_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1369_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1369_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec(v_a_1390_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Rat_ofInt(v_a_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1405_, lean_object* v_v_1406_, lean_object* v_a_1407_){
_start:
{
if (lean_obj_tag(v_a_1407_) == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v_a_1405_);
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_v_1406_);
return v___x_1408_;
}
else
{
lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v_p_1411_; lean_object* v_size_1412_; uint8_t v___x_1413_; 
v_k_1409_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_k_1409_);
v_v_1410_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_v_1410_);
v_p_1411_ = lean_ctor_get(v_a_1407_, 2);
lean_inc(v_p_1411_);
lean_dec_ref(v_a_1407_);
v_size_1412_ = lean_ctor_get(v_a_1405_, 2);
v___x_1413_ = lean_nat_dec_lt(v_v_1410_, v_size_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec(v_p_1411_);
lean_dec(v_v_1410_);
lean_dec(v_k_1409_);
lean_dec_ref(v_v_1406_);
lean_dec_ref(v_a_1405_);
v___x_1414_ = lean_box(0);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1415_ = l_Rat_ofInt(v_k_1409_);
v___x_1416_ = l_instInhabitedRat;
lean_inc_ref(v_a_1405_);
v___x_1417_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1416_, v_a_1405_, v_v_1410_);
lean_dec(v_v_1410_);
v___x_1418_ = l_Rat_mul(v___x_1415_, v___x_1417_);
lean_dec_ref(v___x_1415_);
v___x_1419_ = l_Rat_add(v_v_1406_, v___x_1418_);
v_v_1406_ = v___x_1419_;
v_a_1407_ = v_p_1411_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_nat_to_int(v_a_1421_);
v___x_1423_ = l_Rat_ofInt(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1450_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1450_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1450_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_assignment_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v_assignment_1444_ = lean_ctor_get(v_a_1440_, 35);
lean_inc_ref(v_assignment_1444_);
lean_dec(v_a_1440_);
v___x_1445_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1446_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1444_, v___x_1445_, v_p_1426_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1446_);
v___x_1448_ = v___x_1442_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_p_1426_);
v_a_1451_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1439_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1439_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec(v_a_1460_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_nat_to_int(v_a_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_p_1488_; uint8_t v_strict_1489_; lean_object* v___x_1490_; 
v_p_1488_ = lean_ctor_get(v_c_1475_, 0);
lean_inc(v_p_1488_);
v_strict_1489_ = lean_ctor_get_uint8(v_c_1475_, sizeof(void*)*2);
lean_dec_ref(v_c_1475_);
v___x_1490_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1488_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1516_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1516_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1516_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
if (lean_obj_tag(v_a_1491_) == 1)
{
if (v_strict_1489_ == 0)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v_val_1495_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v_a_1491_);
v___x_1496_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1497_ = l_Rat_instDecidableLe(v_val_1495_, v___x_1496_);
v___x_1498_ = l_Bool_toLBool(v___x_1497_);
v___x_1499_ = lean_box(v___x_1498_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1499_);
v___x_1501_ = v___x_1493_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
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
lean_object* v_val_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v_val_1503_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_val_1503_);
lean_dec_ref(v_a_1491_);
v___x_1504_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1505_ = l_Rat_blt(v_val_1503_, v___x_1504_);
v___x_1506_ = l_Bool_toLBool(v___x_1505_);
v___x_1507_ = lean_box(v___x_1506_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1507_);
v___x_1509_ = v___x_1493_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_dec(v_a_1491_);
v___x_1511_ = 2;
v___x_1512_ = lean_box(v___x_1511_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1512_);
v___x_1514_ = v___x_1493_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
v_a_1517_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1490_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1490_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec(v_a_1526_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_p_1552_; lean_object* v___x_1553_; 
v_p_1552_ = lean_ctor_get(v_c_1539_, 0);
lean_inc(v_p_1552_);
lean_dec_ref(v_c_1539_);
v___x_1553_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1552_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1573_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1573_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1573_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
uint8_t v___y_1559_; 
if (lean_obj_tag(v_a_1554_) == 1)
{
lean_object* v_val_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v_val_1565_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_val_1565_);
lean_dec_ref(v_a_1554_);
v___x_1566_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1567_ = l_instDecidableEqRat_decEq(v_val_1565_, v___x_1566_);
lean_dec(v_val_1565_);
if (v___x_1567_ == 0)
{
uint8_t v___x_1568_; 
v___x_1568_ = 1;
v___y_1559_ = v___x_1568_;
goto v___jp_1558_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = 0;
v___y_1559_ = v___x_1569_;
goto v___jp_1558_;
}
}
else
{
uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1556_);
lean_dec(v_a_1554_);
v___x_1570_ = 2;
v___x_1571_ = lean_box(v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
v___jp_1558_:
{
uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1560_ = l_Bool_toLBool(v___y_1559_);
v___x_1561_ = lean_box(v___x_1560_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1561_);
v___x_1563_ = v___x_1556_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1553_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1553_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec(v_a_1583_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1596_, lean_object* v_x_1597_, lean_object* v_s_1598_){
_start:
{
lean_object* v_structs_1599_; lean_object* v_typeIdOf_1600_; lean_object* v_exprToStructId_1601_; lean_object* v_exprToStructIdEntries_1602_; lean_object* v_forbiddenNatModules_1603_; lean_object* v_natStructs_1604_; lean_object* v_natTypeIdOf_1605_; lean_object* v_exprToNatStructId_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_structs_1599_ = lean_ctor_get(v_s_1598_, 0);
v_typeIdOf_1600_ = lean_ctor_get(v_s_1598_, 1);
v_exprToStructId_1601_ = lean_ctor_get(v_s_1598_, 2);
v_exprToStructIdEntries_1602_ = lean_ctor_get(v_s_1598_, 3);
v_forbiddenNatModules_1603_ = lean_ctor_get(v_s_1598_, 4);
v_natStructs_1604_ = lean_ctor_get(v_s_1598_, 5);
v_natTypeIdOf_1605_ = lean_ctor_get(v_s_1598_, 6);
v_exprToNatStructId_1606_ = lean_ctor_get(v_s_1598_, 7);
v___x_1607_ = lean_array_get_size(v_structs_1599_);
v___x_1608_ = lean_nat_dec_lt(v_a_1596_, v___x_1607_);
if (v___x_1608_ == 0)
{
return v_s_1598_;
}
else
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1670_; 
lean_inc_ref(v_exprToNatStructId_1606_);
lean_inc_ref(v_natTypeIdOf_1605_);
lean_inc_ref(v_natStructs_1604_);
lean_inc_ref(v_forbiddenNatModules_1603_);
lean_inc_ref(v_exprToStructIdEntries_1602_);
lean_inc_ref(v_exprToStructId_1601_);
lean_inc_ref(v_typeIdOf_1600_);
lean_inc_ref(v_structs_1599_);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_s_1598_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; lean_object* v_unused_1677_; lean_object* v_unused_1678_; 
v_unused_1671_ = lean_ctor_get(v_s_1598_, 7);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_s_1598_, 6);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_s_1598_, 5);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_s_1598_, 4);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_s_1598_, 3);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_s_1598_, 2);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_s_1598_, 1);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_s_1598_, 0);
lean_dec(v_unused_1678_);
v___x_1610_ = v_s_1598_;
v_isShared_1611_ = v_isSharedCheck_1670_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_s_1598_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1670_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_v_1612_; lean_object* v_id_1613_; lean_object* v_ringId_x3f_1614_; lean_object* v_type_1615_; lean_object* v_u_1616_; lean_object* v_intModuleInst_1617_; lean_object* v_leInst_x3f_1618_; lean_object* v_ltInst_x3f_1619_; lean_object* v_lawfulOrderLTInst_x3f_1620_; lean_object* v_isPreorderInst_x3f_1621_; lean_object* v_orderedAddInst_x3f_1622_; lean_object* v_isLinearInst_x3f_1623_; lean_object* v_noNatDivInst_x3f_1624_; lean_object* v_ringInst_x3f_1625_; lean_object* v_commRingInst_x3f_1626_; lean_object* v_orderedRingInst_x3f_1627_; lean_object* v_fieldInst_x3f_1628_; lean_object* v_charInst_x3f_1629_; lean_object* v_zero_1630_; lean_object* v_ofNatZero_1631_; lean_object* v_one_x3f_1632_; lean_object* v_leFn_x3f_1633_; lean_object* v_ltFn_x3f_1634_; lean_object* v_addFn_1635_; lean_object* v_zsmulFn_1636_; lean_object* v_nsmulFn_1637_; lean_object* v_zsmulFn_x3f_1638_; lean_object* v_nsmulFn_x3f_1639_; lean_object* v_homomulFn_x3f_1640_; lean_object* v_subFn_1641_; lean_object* v_negFn_1642_; lean_object* v_vars_1643_; lean_object* v_varMap_1644_; lean_object* v_lowers_1645_; lean_object* v_uppers_1646_; lean_object* v_diseqs_1647_; lean_object* v_assignment_1648_; uint8_t v_caseSplits_1649_; lean_object* v_conflict_x3f_1650_; lean_object* v_diseqSplits_1651_; lean_object* v_elimEqs_1652_; lean_object* v_elimStack_1653_; lean_object* v_occurs_1654_; lean_object* v_ignored_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1669_; 
v_v_1612_ = lean_array_fget(v_structs_1599_, v_a_1596_);
v_id_1613_ = lean_ctor_get(v_v_1612_, 0);
v_ringId_x3f_1614_ = lean_ctor_get(v_v_1612_, 1);
v_type_1615_ = lean_ctor_get(v_v_1612_, 2);
v_u_1616_ = lean_ctor_get(v_v_1612_, 3);
v_intModuleInst_1617_ = lean_ctor_get(v_v_1612_, 4);
v_leInst_x3f_1618_ = lean_ctor_get(v_v_1612_, 5);
v_ltInst_x3f_1619_ = lean_ctor_get(v_v_1612_, 6);
v_lawfulOrderLTInst_x3f_1620_ = lean_ctor_get(v_v_1612_, 7);
v_isPreorderInst_x3f_1621_ = lean_ctor_get(v_v_1612_, 8);
v_orderedAddInst_x3f_1622_ = lean_ctor_get(v_v_1612_, 9);
v_isLinearInst_x3f_1623_ = lean_ctor_get(v_v_1612_, 10);
v_noNatDivInst_x3f_1624_ = lean_ctor_get(v_v_1612_, 11);
v_ringInst_x3f_1625_ = lean_ctor_get(v_v_1612_, 12);
v_commRingInst_x3f_1626_ = lean_ctor_get(v_v_1612_, 13);
v_orderedRingInst_x3f_1627_ = lean_ctor_get(v_v_1612_, 14);
v_fieldInst_x3f_1628_ = lean_ctor_get(v_v_1612_, 15);
v_charInst_x3f_1629_ = lean_ctor_get(v_v_1612_, 16);
v_zero_1630_ = lean_ctor_get(v_v_1612_, 17);
v_ofNatZero_1631_ = lean_ctor_get(v_v_1612_, 18);
v_one_x3f_1632_ = lean_ctor_get(v_v_1612_, 19);
v_leFn_x3f_1633_ = lean_ctor_get(v_v_1612_, 20);
v_ltFn_x3f_1634_ = lean_ctor_get(v_v_1612_, 21);
v_addFn_1635_ = lean_ctor_get(v_v_1612_, 22);
v_zsmulFn_1636_ = lean_ctor_get(v_v_1612_, 23);
v_nsmulFn_1637_ = lean_ctor_get(v_v_1612_, 24);
v_zsmulFn_x3f_1638_ = lean_ctor_get(v_v_1612_, 25);
v_nsmulFn_x3f_1639_ = lean_ctor_get(v_v_1612_, 26);
v_homomulFn_x3f_1640_ = lean_ctor_get(v_v_1612_, 27);
v_subFn_1641_ = lean_ctor_get(v_v_1612_, 28);
v_negFn_1642_ = lean_ctor_get(v_v_1612_, 29);
v_vars_1643_ = lean_ctor_get(v_v_1612_, 30);
v_varMap_1644_ = lean_ctor_get(v_v_1612_, 31);
v_lowers_1645_ = lean_ctor_get(v_v_1612_, 32);
v_uppers_1646_ = lean_ctor_get(v_v_1612_, 33);
v_diseqs_1647_ = lean_ctor_get(v_v_1612_, 34);
v_assignment_1648_ = lean_ctor_get(v_v_1612_, 35);
v_caseSplits_1649_ = lean_ctor_get_uint8(v_v_1612_, sizeof(void*)*42);
v_conflict_x3f_1650_ = lean_ctor_get(v_v_1612_, 36);
v_diseqSplits_1651_ = lean_ctor_get(v_v_1612_, 37);
v_elimEqs_1652_ = lean_ctor_get(v_v_1612_, 38);
v_elimStack_1653_ = lean_ctor_get(v_v_1612_, 39);
v_occurs_1654_ = lean_ctor_get(v_v_1612_, 40);
v_ignored_1655_ = lean_ctor_get(v_v_1612_, 41);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_v_1612_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1657_ = v_v_1612_;
v_isShared_1658_ = v_isSharedCheck_1669_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_ignored_1655_);
lean_inc(v_occurs_1654_);
lean_inc(v_elimStack_1653_);
lean_inc(v_elimEqs_1652_);
lean_inc(v_diseqSplits_1651_);
lean_inc(v_conflict_x3f_1650_);
lean_inc(v_assignment_1648_);
lean_inc(v_diseqs_1647_);
lean_inc(v_uppers_1646_);
lean_inc(v_lowers_1645_);
lean_inc(v_varMap_1644_);
lean_inc(v_vars_1643_);
lean_inc(v_negFn_1642_);
lean_inc(v_subFn_1641_);
lean_inc(v_homomulFn_x3f_1640_);
lean_inc(v_nsmulFn_x3f_1639_);
lean_inc(v_zsmulFn_x3f_1638_);
lean_inc(v_nsmulFn_1637_);
lean_inc(v_zsmulFn_1636_);
lean_inc(v_addFn_1635_);
lean_inc(v_ltFn_x3f_1634_);
lean_inc(v_leFn_x3f_1633_);
lean_inc(v_one_x3f_1632_);
lean_inc(v_ofNatZero_1631_);
lean_inc(v_zero_1630_);
lean_inc(v_charInst_x3f_1629_);
lean_inc(v_fieldInst_x3f_1628_);
lean_inc(v_orderedRingInst_x3f_1627_);
lean_inc(v_commRingInst_x3f_1626_);
lean_inc(v_ringInst_x3f_1625_);
lean_inc(v_noNatDivInst_x3f_1624_);
lean_inc(v_isLinearInst_x3f_1623_);
lean_inc(v_orderedAddInst_x3f_1622_);
lean_inc(v_isPreorderInst_x3f_1621_);
lean_inc(v_lawfulOrderLTInst_x3f_1620_);
lean_inc(v_ltInst_x3f_1619_);
lean_inc(v_leInst_x3f_1618_);
lean_inc(v_intModuleInst_1617_);
lean_inc(v_u_1616_);
lean_inc(v_type_1615_);
lean_inc(v_ringId_x3f_1614_);
lean_inc(v_id_1613_);
lean_dec(v_v_1612_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1669_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v_xs_x27_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1659_ = lean_box(0);
v_xs_x27_1660_ = lean_array_fset(v_structs_1599_, v_a_1596_, v___x_1659_);
v___x_1661_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1648_, v_x_1597_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 35, v___x_1661_);
v___x_1663_ = v___x_1657_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_id_1613_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_ringId_x3f_1614_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_type_1615_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_u_1616_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_intModuleInst_1617_);
lean_ctor_set(v_reuseFailAlloc_1668_, 5, v_leInst_x3f_1618_);
lean_ctor_set(v_reuseFailAlloc_1668_, 6, v_ltInst_x3f_1619_);
lean_ctor_set(v_reuseFailAlloc_1668_, 7, v_lawfulOrderLTInst_x3f_1620_);
lean_ctor_set(v_reuseFailAlloc_1668_, 8, v_isPreorderInst_x3f_1621_);
lean_ctor_set(v_reuseFailAlloc_1668_, 9, v_orderedAddInst_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1668_, 10, v_isLinearInst_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1668_, 11, v_noNatDivInst_x3f_1624_);
lean_ctor_set(v_reuseFailAlloc_1668_, 12, v_ringInst_x3f_1625_);
lean_ctor_set(v_reuseFailAlloc_1668_, 13, v_commRingInst_x3f_1626_);
lean_ctor_set(v_reuseFailAlloc_1668_, 14, v_orderedRingInst_x3f_1627_);
lean_ctor_set(v_reuseFailAlloc_1668_, 15, v_fieldInst_x3f_1628_);
lean_ctor_set(v_reuseFailAlloc_1668_, 16, v_charInst_x3f_1629_);
lean_ctor_set(v_reuseFailAlloc_1668_, 17, v_zero_1630_);
lean_ctor_set(v_reuseFailAlloc_1668_, 18, v_ofNatZero_1631_);
lean_ctor_set(v_reuseFailAlloc_1668_, 19, v_one_x3f_1632_);
lean_ctor_set(v_reuseFailAlloc_1668_, 20, v_leFn_x3f_1633_);
lean_ctor_set(v_reuseFailAlloc_1668_, 21, v_ltFn_x3f_1634_);
lean_ctor_set(v_reuseFailAlloc_1668_, 22, v_addFn_1635_);
lean_ctor_set(v_reuseFailAlloc_1668_, 23, v_zsmulFn_1636_);
lean_ctor_set(v_reuseFailAlloc_1668_, 24, v_nsmulFn_1637_);
lean_ctor_set(v_reuseFailAlloc_1668_, 25, v_zsmulFn_x3f_1638_);
lean_ctor_set(v_reuseFailAlloc_1668_, 26, v_nsmulFn_x3f_1639_);
lean_ctor_set(v_reuseFailAlloc_1668_, 27, v_homomulFn_x3f_1640_);
lean_ctor_set(v_reuseFailAlloc_1668_, 28, v_subFn_1641_);
lean_ctor_set(v_reuseFailAlloc_1668_, 29, v_negFn_1642_);
lean_ctor_set(v_reuseFailAlloc_1668_, 30, v_vars_1643_);
lean_ctor_set(v_reuseFailAlloc_1668_, 31, v_varMap_1644_);
lean_ctor_set(v_reuseFailAlloc_1668_, 32, v_lowers_1645_);
lean_ctor_set(v_reuseFailAlloc_1668_, 33, v_uppers_1646_);
lean_ctor_set(v_reuseFailAlloc_1668_, 34, v_diseqs_1647_);
lean_ctor_set(v_reuseFailAlloc_1668_, 35, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1668_, 36, v_conflict_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1668_, 37, v_diseqSplits_1651_);
lean_ctor_set(v_reuseFailAlloc_1668_, 38, v_elimEqs_1652_);
lean_ctor_set(v_reuseFailAlloc_1668_, 39, v_elimStack_1653_);
lean_ctor_set(v_reuseFailAlloc_1668_, 40, v_occurs_1654_);
lean_ctor_set(v_reuseFailAlloc_1668_, 41, v_ignored_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1668_, sizeof(void*)*42, v_caseSplits_1649_);
v___x_1663_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_array_fset(v_xs_x27_1660_, v_a_1596_, v___x_1663_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1664_);
v___x_1666_ = v___x_1610_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_typeIdOf_1600_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_exprToStructId_1601_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_exprToStructIdEntries_1602_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_forbiddenNatModules_1603_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_natStructs_1604_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_natTypeIdOf_1605_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_exprToNatStructId_1606_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1679_, lean_object* v_x_1680_, lean_object* v_s_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1679_, v_x_1680_, v_s_1681_);
lean_dec(v_x_1680_);
lean_dec(v_a_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_inc(v_a_1684_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1687_, 0, v_a_1684_);
lean_closure_set(v___f_1687_, 1, v_x_1683_);
v___x_1688_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1689_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1688_, v___f_1687_, v_a_1685_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec(v_a_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1695_, v_a_1696_, v_a_1697_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec(v_a_1710_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1753_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_vars_1741_; lean_object* v_size_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_vars_1741_ = lean_ctor_get(v_a_1737_, 30);
lean_inc_ref(v_vars_1741_);
lean_dec(v_a_1737_);
v_size_1742_ = lean_ctor_get(v_vars_1741_, 2);
v___x_1743_ = l_Lean_instInhabitedExpr;
v___x_1744_ = lean_nat_dec_lt(v_x_1723_, v_size_1742_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec_ref(v_vars_1741_);
v___x_1745_ = l_outOfBounds___redArg(v___x_1743_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1745_);
v___x_1747_ = v___x_1739_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1743_, v_vars_1741_, v_x_1723_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1749_);
v___x_1751_ = v___x_1739_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1736_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1736_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec(v_x_1762_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1777_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; uint8_t v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
v___x_1790_ = lean_unbox(v_a_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v___x_1788_);
v___x_1791_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1805_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1805_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1805_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_conflict_x3f_1796_; 
v_conflict_x3f_1796_ = lean_ctor_get(v_a_1792_, 36);
lean_inc(v_conflict_x3f_1796_);
lean_dec(v_a_1792_);
if (lean_obj_tag(v_conflict_x3f_1796_) == 0)
{
lean_object* v___x_1798_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v_a_1789_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1789_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
else
{
uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_dec_ref(v_conflict_x3f_1796_);
lean_dec(v_a_1789_);
v___x_1800_ = 1;
v___x_1801_ = lean_box(v___x_1800_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1801_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1789_);
v_a_1806_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1791_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1791_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_dec(v_a_1789_);
return v___x_1788_;
}
}
else
{
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec(v_a_1814_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1863_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___y_1846_; lean_object* v_elimEqs_1857_; lean_object* v_size_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v_elimEqs_1857_ = lean_ctor_get(v_a_1841_, 38);
lean_inc_ref(v_elimEqs_1857_);
lean_dec(v_a_1841_);
v_size_1858_ = lean_ctor_get(v_elimEqs_1857_, 2);
v___x_1859_ = lean_box(0);
v___x_1860_ = lean_nat_dec_lt(v_x_1827_, v_size_1858_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_elimEqs_1857_);
v___x_1861_ = l_outOfBounds___redArg(v___x_1859_);
v___y_1846_ = v___x_1861_;
goto v___jp_1845_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1859_, v_elimEqs_1857_, v_x_1827_);
v___y_1846_ = v___x_1862_;
goto v___jp_1845_;
}
v___jp_1845_:
{
if (lean_obj_tag(v___y_1846_) == 0)
{
uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = 0;
v___x_1848_ = lean_box(v___x_1847_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1848_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec_ref(v___y_1846_);
v___x_1852_ = 1;
v___x_1853_ = lean_box(v___x_1852_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1853_);
v___x_1855_ = v___x_1843_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1840_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1840_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec(v_x_1872_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1916_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1916_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_occurs_1904_; lean_object* v_size_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_occurs_1904_ = lean_ctor_get(v_a_1900_, 40);
lean_inc_ref(v_occurs_1904_);
lean_dec(v_a_1900_);
v_size_1905_ = lean_ctor_get(v_occurs_1904_, 2);
v___x_1906_ = lean_box(1);
v___x_1907_ = lean_nat_dec_lt(v_x_1886_, v_size_1905_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_dec_ref(v_occurs_1904_);
v___x_1908_ = l_outOfBounds___redArg(v___x_1906_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1908_);
v___x_1910_ = v___x_1902_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1906_, v_occurs_1904_, v_x_1886_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1912_);
v___x_1914_ = v___x_1902_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1899_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec(v_x_1925_);
return v_res_1938_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1939_, lean_object* v_t_1940_){
_start:
{
if (lean_obj_tag(v_t_1940_) == 0)
{
lean_object* v_k_1941_; lean_object* v_l_1942_; lean_object* v_r_1943_; uint8_t v___x_1944_; 
v_k_1941_ = lean_ctor_get(v_t_1940_, 1);
v_l_1942_ = lean_ctor_get(v_t_1940_, 3);
v_r_1943_ = lean_ctor_get(v_t_1940_, 4);
v___x_1944_ = lean_nat_dec_lt(v_k_1939_, v_k_1941_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_eq(v_k_1939_, v_k_1941_);
if (v___x_1945_ == 0)
{
v_t_1940_ = v_r_1943_;
goto _start;
}
else
{
return v___x_1945_;
}
}
else
{
v_t_1940_ = v_l_1942_;
goto _start;
}
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = 0;
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1949_, lean_object* v_t_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1949_, v_t_1950_);
lean_dec(v_t_1950_);
lean_dec(v_k_1949_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1953_, lean_object* v_v_1954_, lean_object* v_t_1955_){
_start:
{
if (lean_obj_tag(v_t_1955_) == 0)
{
lean_object* v_size_1956_; lean_object* v_k_1957_; lean_object* v_v_1958_; lean_object* v_l_1959_; lean_object* v_r_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2241_; 
v_size_1956_ = lean_ctor_get(v_t_1955_, 0);
v_k_1957_ = lean_ctor_get(v_t_1955_, 1);
v_v_1958_ = lean_ctor_get(v_t_1955_, 2);
v_l_1959_ = lean_ctor_get(v_t_1955_, 3);
v_r_1960_ = lean_ctor_get(v_t_1955_, 4);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_t_1955_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_1962_ = v_t_1955_;
v_isShared_1963_ = v_isSharedCheck_2241_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_r_1960_);
lean_inc(v_l_1959_);
lean_inc(v_v_1958_);
lean_inc(v_k_1957_);
lean_inc(v_size_1956_);
lean_dec(v_t_1955_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2241_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_nat_dec_lt(v_k_1953_, v_k_1957_);
if (v___x_1964_ == 0)
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_nat_dec_eq(v_k_1953_, v_k_1957_);
if (v___x_1965_ == 0)
{
lean_object* v_impl_1966_; lean_object* v___x_1967_; 
lean_dec(v_size_1956_);
v_impl_1966_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1953_, v_v_1954_, v_r_1960_);
v___x_1967_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1959_) == 0)
{
lean_object* v_size_1968_; lean_object* v_size_1969_; lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v_l_1972_; lean_object* v_r_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_size_1968_ = lean_ctor_get(v_l_1959_, 0);
v_size_1969_ = lean_ctor_get(v_impl_1966_, 0);
lean_inc(v_size_1969_);
v_k_1970_ = lean_ctor_get(v_impl_1966_, 1);
lean_inc(v_k_1970_);
v_v_1971_ = lean_ctor_get(v_impl_1966_, 2);
lean_inc(v_v_1971_);
v_l_1972_ = lean_ctor_get(v_impl_1966_, 3);
lean_inc(v_l_1972_);
v_r_1973_ = lean_ctor_get(v_impl_1966_, 4);
lean_inc(v_r_1973_);
v___x_1974_ = lean_unsigned_to_nat(3u);
v___x_1975_ = lean_nat_mul(v___x_1974_, v_size_1968_);
v___x_1976_ = lean_nat_dec_lt(v___x_1975_, v_size_1969_);
lean_dec(v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v_r_1973_);
lean_dec(v_l_1972_);
lean_dec(v_v_1971_);
lean_dec(v_k_1970_);
v___x_1977_ = lean_nat_add(v___x_1967_, v_size_1968_);
v___x_1978_ = lean_nat_add(v___x_1977_, v_size_1969_);
lean_dec(v_size_1969_);
lean_dec(v___x_1977_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_impl_1966_);
lean_ctor_set(v___x_1962_, 0, v___x_1978_);
v___x_1980_ = v___x_1962_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_l_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_impl_1966_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v_impl_1966_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2046_ = lean_ctor_get(v_impl_1966_, 4);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_impl_1966_, 3);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_impl_1966_, 2);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_impl_1966_, 1);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_impl_1966_, 0);
lean_dec(v_unused_2050_);
v___x_1983_ = v_impl_1966_;
v_isShared_1984_ = v_isSharedCheck_2045_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_impl_1966_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2045_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_size_1985_; lean_object* v_k_1986_; lean_object* v_v_1987_; lean_object* v_l_1988_; lean_object* v_r_1989_; lean_object* v_size_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_size_1985_ = lean_ctor_get(v_l_1972_, 0);
v_k_1986_ = lean_ctor_get(v_l_1972_, 1);
v_v_1987_ = lean_ctor_get(v_l_1972_, 2);
v_l_1988_ = lean_ctor_get(v_l_1972_, 3);
v_r_1989_ = lean_ctor_get(v_l_1972_, 4);
v_size_1990_ = lean_ctor_get(v_r_1973_, 0);
v___x_1991_ = lean_unsigned_to_nat(2u);
v___x_1992_ = lean_nat_mul(v___x_1991_, v_size_1990_);
v___x_1993_ = lean_nat_dec_lt(v_size_1985_, v___x_1992_);
lean_dec(v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2021_; 
lean_inc(v_r_1989_);
lean_inc(v_l_1988_);
lean_inc(v_v_1987_);
lean_inc(v_k_1986_);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_l_1972_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; 
v_unused_2022_ = lean_ctor_get(v_l_1972_, 4);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_l_1972_, 3);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_l_1972_, 2);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_l_1972_, 1);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_l_1972_, 0);
lean_dec(v_unused_2026_);
v___x_1995_ = v_l_1972_;
v_isShared_1996_ = v_isSharedCheck_2021_;
goto v_resetjp_1994_;
}
else
{
lean_dec(v_l_1972_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2021_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2011_; 
v___x_1997_ = lean_nat_add(v___x_1967_, v_size_1968_);
v___x_1998_ = lean_nat_add(v___x_1997_, v_size_1969_);
lean_dec(v_size_1969_);
if (lean_obj_tag(v_l_1988_) == 0)
{
lean_object* v_size_2019_; 
v_size_2019_ = lean_ctor_get(v_l_1988_, 0);
lean_inc(v_size_2019_);
v___y_2011_ = v_size_2019_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___y_2011_ = v___x_2020_;
goto v___jp_2010_;
}
v___jp_1999_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_nat_add(v___y_2000_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec(v___y_2000_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 4, v_r_1973_);
lean_ctor_set(v___x_1995_, 3, v_r_1989_);
lean_ctor_set(v___x_1995_, 2, v_v_1971_);
lean_ctor_set(v___x_1995_, 1, v_k_1970_);
lean_ctor_set(v___x_1995_, 0, v___x_2003_);
v___x_2005_ = v___x_1995_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_r_1989_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_r_1973_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v___x_2005_);
lean_ctor_set(v___x_1983_, 3, v___y_2001_);
lean_ctor_set(v___x_1983_, 2, v_v_1987_);
lean_ctor_set(v___x_1983_, 1, v_k_1986_);
lean_ctor_set(v___x_1983_, 0, v___x_1998_);
v___x_2007_ = v___x_1983_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_k_1986_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_v_1987_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v___y_2001_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_nat_add(v___x_1997_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec(v___x_1997_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_l_1988_);
lean_ctor_set(v___x_1962_, 0, v___x_2012_);
v___x_2014_ = v___x_1962_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_l_1959_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_l_1988_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_nat_add(v___x_1967_, v_size_1990_);
if (lean_obj_tag(v_r_1989_) == 0)
{
lean_object* v_size_2016_; 
v_size_2016_ = lean_ctor_get(v_r_1989_, 0);
lean_inc(v_size_2016_);
v___y_2000_ = v___x_2015_;
v___y_2001_ = v___x_2014_;
v___y_2002_ = v_size_2016_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v___y_2000_ = v___x_2015_;
v___y_2001_ = v___x_2014_;
v___y_2002_ = v___x_2017_;
goto v___jp_1999_;
}
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_del_object(v___x_1962_);
v___x_2027_ = lean_nat_add(v___x_1967_, v_size_1968_);
v___x_2028_ = lean_nat_add(v___x_2027_, v_size_1969_);
lean_dec(v_size_1969_);
v___x_2029_ = lean_nat_add(v___x_2027_, v_size_1985_);
lean_dec(v___x_2027_);
lean_inc_ref(v_l_1959_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v_l_1972_);
lean_ctor_set(v___x_1983_, 3, v_l_1959_);
lean_ctor_set(v___x_1983_, 2, v_v_1958_);
lean_ctor_set(v___x_1983_, 1, v_k_1957_);
lean_ctor_set(v___x_1983_, 0, v___x_2029_);
v___x_2031_ = v___x_1983_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1959_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_l_1972_);
v___x_2031_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_isSharedCheck_2038_ = !lean_is_exclusive(v_l_1959_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2039_ = lean_ctor_get(v_l_1959_, 4);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_l_1959_, 3);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_l_1959_, 2);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_l_1959_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_l_1959_, 0);
lean_dec(v_unused_2043_);
v___x_2033_ = v_l_1959_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_l_1959_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 4, v_r_1973_);
lean_ctor_set(v___x_2033_, 3, v___x_2031_);
lean_ctor_set(v___x_2033_, 2, v_v_1971_);
lean_ctor_set(v___x_2033_, 1, v_k_1970_);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_r_1973_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2051_; 
v_l_2051_ = lean_ctor_get(v_impl_1966_, 3);
lean_inc(v_l_2051_);
if (lean_obj_tag(v_l_2051_) == 0)
{
lean_object* v_r_2052_; lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2077_; 
v_r_2052_ = lean_ctor_get(v_impl_1966_, 4);
v_k_2053_ = lean_ctor_get(v_impl_1966_, 1);
v_v_2054_ = lean_ctor_get(v_impl_1966_, 2);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_impl_1966_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; lean_object* v_unused_2079_; 
v_unused_2078_ = lean_ctor_get(v_impl_1966_, 3);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_1966_, 0);
lean_dec(v_unused_2079_);
v___x_2056_ = v_impl_1966_;
v_isShared_2057_ = v_isSharedCheck_2077_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_r_2052_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
lean_dec(v_impl_1966_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2077_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_k_2058_; lean_object* v_v_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v_k_2058_ = lean_ctor_get(v_l_2051_, 1);
v_v_2059_ = lean_ctor_get(v_l_2051_, 2);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_l_2051_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; lean_object* v_unused_2075_; lean_object* v_unused_2076_; 
v_unused_2074_ = lean_ctor_get(v_l_2051_, 4);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_l_2051_, 3);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_l_2051_, 0);
lean_dec(v_unused_2076_);
v___x_2061_ = v_l_2051_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_v_2059_);
lean_inc(v_k_2058_);
lean_dec(v_l_2051_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2052_, 2);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_r_2052_);
lean_ctor_set(v___x_2061_, 3, v_r_2052_);
lean_ctor_set(v___x_2061_, 2, v_v_1958_);
lean_ctor_set(v___x_2061_, 1, v_k_1957_);
lean_ctor_set(v___x_2061_, 0, v___x_1967_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_r_2052_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_r_2052_);
v___x_2065_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
lean_inc(v_r_2052_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 3, v_r_2052_);
lean_ctor_set(v___x_2056_, 0, v___x_1967_);
v___x_2067_ = v___x_2056_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_k_2053_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_v_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_r_2052_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_r_2052_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v___x_2067_);
lean_ctor_set(v___x_1962_, 3, v___x_2065_);
lean_ctor_set(v___x_1962_, 2, v_v_2059_);
lean_ctor_set(v___x_1962_, 1, v_k_2058_);
lean_ctor_set(v___x_1962_, 0, v___x_2063_);
v___x_2069_ = v___x_1962_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_2058_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_2059_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
else
{
lean_object* v_r_2080_; 
v_r_2080_ = lean_ctor_get(v_impl_1966_, 4);
lean_inc(v_r_2080_);
if (lean_obj_tag(v_r_2080_) == 0)
{
lean_object* v_k_2081_; lean_object* v_v_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2093_; 
v_k_2081_ = lean_ctor_get(v_impl_1966_, 1);
v_v_2082_ = lean_ctor_get(v_impl_1966_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_impl_1966_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_impl_1966_, 4);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_impl_1966_, 3);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_impl_1966_, 0);
lean_dec(v_unused_2096_);
v___x_2084_ = v_impl_1966_;
v_isShared_2085_ = v_isSharedCheck_2093_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_v_2082_);
lean_inc(v_k_2081_);
lean_dec(v_impl_1966_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2093_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_unsigned_to_nat(3u);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 4, v_l_2051_);
lean_ctor_set(v___x_2084_, 2, v_v_1958_);
lean_ctor_set(v___x_2084_, 1, v_k_1957_);
lean_ctor_set(v___x_2084_, 0, v___x_1967_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_2051_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_l_2051_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_r_2080_);
lean_ctor_set(v___x_1962_, 3, v___x_2088_);
lean_ctor_set(v___x_1962_, 2, v_v_2082_);
lean_ctor_set(v___x_1962_, 1, v_k_2081_);
lean_ctor_set(v___x_1962_, 0, v___x_2086_);
v___x_2090_ = v___x_1962_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_2081_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_2082_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_r_2080_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = lean_unsigned_to_nat(2u);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_impl_1966_);
lean_ctor_set(v___x_1962_, 3, v_r_2080_);
lean_ctor_set(v___x_1962_, 0, v___x_2097_);
v___x_2099_ = v___x_1962_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_r_2080_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_impl_1966_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v___x_2102_; 
lean_dec(v_v_1958_);
lean_dec(v_k_1957_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 2, v_v_1954_);
lean_ctor_set(v___x_1962_, 1, v_k_1953_);
v___x_2102_ = v___x_1962_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_size_1956_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_l_1959_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_1960_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_impl_2104_; lean_object* v___x_2105_; 
lean_dec(v_size_1956_);
v_impl_2104_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1953_, v_v_1954_, v_l_1959_);
v___x_2105_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1960_) == 0)
{
lean_object* v_size_2106_; lean_object* v_size_2107_; lean_object* v_k_2108_; lean_object* v_v_2109_; lean_object* v_l_2110_; lean_object* v_r_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_size_2106_ = lean_ctor_get(v_r_1960_, 0);
v_size_2107_ = lean_ctor_get(v_impl_2104_, 0);
lean_inc(v_size_2107_);
v_k_2108_ = lean_ctor_get(v_impl_2104_, 1);
lean_inc(v_k_2108_);
v_v_2109_ = lean_ctor_get(v_impl_2104_, 2);
lean_inc(v_v_2109_);
v_l_2110_ = lean_ctor_get(v_impl_2104_, 3);
lean_inc(v_l_2110_);
v_r_2111_ = lean_ctor_get(v_impl_2104_, 4);
lean_inc(v_r_2111_);
v___x_2112_ = lean_unsigned_to_nat(3u);
v___x_2113_ = lean_nat_mul(v___x_2112_, v_size_2106_);
v___x_2114_ = lean_nat_dec_lt(v___x_2113_, v_size_2107_);
lean_dec(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_r_2111_);
lean_dec(v_l_2110_);
lean_dec(v_v_2109_);
lean_dec(v_k_2108_);
v___x_2115_ = lean_nat_add(v___x_2105_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2116_ = lean_nat_add(v___x_2115_, v_size_2106_);
lean_dec(v___x_2115_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 3, v_impl_2104_);
lean_ctor_set(v___x_1962_, 0, v___x_2116_);
v___x_2118_ = v___x_1962_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_impl_2104_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_r_1960_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2185_; 
v_isSharedCheck_2185_ = !lean_is_exclusive(v_impl_2104_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2186_ = lean_ctor_get(v_impl_2104_, 4);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_impl_2104_, 3);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_impl_2104_, 2);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_impl_2104_, 1);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_impl_2104_, 0);
lean_dec(v_unused_2190_);
v___x_2121_ = v_impl_2104_;
v_isShared_2122_ = v_isSharedCheck_2185_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v_impl_2104_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2185_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_size_2123_; lean_object* v_size_2124_; lean_object* v_k_2125_; lean_object* v_v_2126_; lean_object* v_l_2127_; lean_object* v_r_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_size_2123_ = lean_ctor_get(v_l_2110_, 0);
v_size_2124_ = lean_ctor_get(v_r_2111_, 0);
v_k_2125_ = lean_ctor_get(v_r_2111_, 1);
v_v_2126_ = lean_ctor_get(v_r_2111_, 2);
v_l_2127_ = lean_ctor_get(v_r_2111_, 3);
v_r_2128_ = lean_ctor_get(v_r_2111_, 4);
v___x_2129_ = lean_unsigned_to_nat(2u);
v___x_2130_ = lean_nat_mul(v___x_2129_, v_size_2123_);
v___x_2131_ = lean_nat_dec_lt(v_size_2124_, v___x_2130_);
lean_dec(v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2160_; 
lean_inc(v_r_2128_);
lean_inc(v_l_2127_);
lean_inc(v_v_2126_);
lean_inc(v_k_2125_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_r_2111_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2161_ = lean_ctor_get(v_r_2111_, 4);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_r_2111_, 3);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_r_2111_, 2);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_r_2111_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_r_2111_, 0);
lean_dec(v_unused_2165_);
v___x_2133_ = v_r_2111_;
v_isShared_2134_ = v_isSharedCheck_2160_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v_r_2111_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2160_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___x_2148_; lean_object* v___y_2150_; 
v___x_2135_ = lean_nat_add(v___x_2105_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2106_);
lean_dec(v___x_2135_);
v___x_2148_ = lean_nat_add(v___x_2105_, v_size_2123_);
if (lean_obj_tag(v_l_2127_) == 0)
{
lean_object* v_size_2158_; 
v_size_2158_ = lean_ctor_get(v_l_2127_, 0);
lean_inc(v_size_2158_);
v___y_2150_ = v_size_2158_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_unsigned_to_nat(0u);
v___y_2150_ = v___x_2159_;
goto v___jp_2149_;
}
v___jp_2137_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_nat_add(v___y_2138_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec(v___y_2138_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_1960_);
lean_ctor_set(v___x_2133_, 3, v_r_2128_);
lean_ctor_set(v___x_2133_, 2, v_v_1958_);
lean_ctor_set(v___x_2133_, 1, v_k_1957_);
lean_ctor_set(v___x_2133_, 0, v___x_2141_);
v___x_2143_ = v___x_2133_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_r_2128_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_r_1960_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2145_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 4, v___x_2143_);
lean_ctor_set(v___x_2121_, 3, v___y_2139_);
lean_ctor_set(v___x_2121_, 2, v_v_2126_);
lean_ctor_set(v___x_2121_, 1, v_k_2125_);
lean_ctor_set(v___x_2121_, 0, v___x_2136_);
v___x_2145_ = v___x_2121_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2125_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2126_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v___y_2139_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
v___jp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_nat_add(v___x_2148_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec(v___x_2148_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_l_2127_);
lean_ctor_set(v___x_1962_, 3, v_l_2110_);
lean_ctor_set(v___x_1962_, 2, v_v_2109_);
lean_ctor_set(v___x_1962_, 1, v_k_2108_);
lean_ctor_set(v___x_1962_, 0, v___x_2151_);
v___x_2153_ = v___x_1962_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_l_2127_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_nat_add(v___x_2105_, v_size_2106_);
if (lean_obj_tag(v_r_2128_) == 0)
{
lean_object* v_size_2155_; 
v_size_2155_ = lean_ctor_get(v_r_2128_, 0);
lean_inc(v_size_2155_);
v___y_2138_ = v___x_2154_;
v___y_2139_ = v___x_2153_;
v___y_2140_ = v_size_2155_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___y_2138_ = v___x_2154_;
v___y_2139_ = v___x_2153_;
v___y_2140_ = v___x_2156_;
goto v___jp_2137_;
}
}
}
}
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_del_object(v___x_1962_);
v___x_2166_ = lean_nat_add(v___x_2105_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2167_ = lean_nat_add(v___x_2166_, v_size_2106_);
lean_dec(v___x_2166_);
v___x_2168_ = lean_nat_add(v___x_2105_, v_size_2106_);
v___x_2169_ = lean_nat_add(v___x_2168_, v_size_2124_);
lean_dec(v___x_2168_);
lean_inc_ref(v_r_1960_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 4, v_r_1960_);
lean_ctor_set(v___x_2121_, 3, v_r_2111_);
lean_ctor_set(v___x_2121_, 2, v_v_1958_);
lean_ctor_set(v___x_2121_, 1, v_k_1957_);
lean_ctor_set(v___x_2121_, 0, v___x_2169_);
v___x_2171_ = v___x_2121_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_r_2111_);
lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_r_1960_);
v___x_2171_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_isSharedCheck_2178_ = !lean_is_exclusive(v_r_1960_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2179_ = lean_ctor_get(v_r_1960_, 4);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_r_1960_, 3);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_r_1960_, 2);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_r_1960_, 1);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_r_1960_, 0);
lean_dec(v_unused_2183_);
v___x_2173_ = v_r_1960_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_dec(v_r_1960_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 4, v___x_2171_);
lean_ctor_set(v___x_2173_, 3, v_l_2110_);
lean_ctor_set(v___x_2173_, 2, v_v_2109_);
lean_ctor_set(v___x_2173_, 1, v_k_2108_);
lean_ctor_set(v___x_2173_, 0, v___x_2167_);
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v___x_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2191_; 
v_l_2191_ = lean_ctor_get(v_impl_2104_, 3);
lean_inc(v_l_2191_);
if (lean_obj_tag(v_l_2191_) == 0)
{
lean_object* v_r_2192_; lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2205_; 
v_r_2192_ = lean_ctor_get(v_impl_2104_, 4);
v_k_2193_ = lean_ctor_get(v_impl_2104_, 1);
v_v_2194_ = lean_ctor_get(v_impl_2104_, 2);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_impl_2104_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; lean_object* v_unused_2207_; 
v_unused_2206_ = lean_ctor_get(v_impl_2104_, 3);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_impl_2104_, 0);
lean_dec(v_unused_2207_);
v___x_2196_ = v_impl_2104_;
v_isShared_2197_ = v_isSharedCheck_2205_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_r_2192_);
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_impl_2104_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2205_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2192_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v_r_2192_);
lean_ctor_set(v___x_2196_, 2, v_v_1958_);
lean_ctor_set(v___x_2196_, 1, v_k_1957_);
lean_ctor_set(v___x_2196_, 0, v___x_2105_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_r_2192_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_r_2192_);
v___x_2200_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v___x_2200_);
lean_ctor_set(v___x_1962_, 3, v_l_2191_);
lean_ctor_set(v___x_1962_, 2, v_v_2194_);
lean_ctor_set(v___x_1962_, 1, v_k_2193_);
lean_ctor_set(v___x_1962_, 0, v___x_2198_);
v___x_2202_ = v___x_1962_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_k_2193_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_v_2194_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_l_2191_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_r_2208_; 
v_r_2208_ = lean_ctor_get(v_impl_2104_, 4);
lean_inc(v_r_2208_);
if (lean_obj_tag(v_r_2208_) == 0)
{
lean_object* v_k_2209_; lean_object* v_v_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2233_; 
v_k_2209_ = lean_ctor_get(v_impl_2104_, 1);
v_v_2210_ = lean_ctor_get(v_impl_2104_, 2);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_impl_2104_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; 
v_unused_2234_ = lean_ctor_get(v_impl_2104_, 4);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_impl_2104_, 3);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_impl_2104_, 0);
lean_dec(v_unused_2236_);
v___x_2212_ = v_impl_2104_;
v_isShared_2213_ = v_isSharedCheck_2233_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_v_2210_);
lean_inc(v_k_2209_);
lean_dec(v_impl_2104_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2233_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_k_2214_; lean_object* v_v_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2229_; 
v_k_2214_ = lean_ctor_get(v_r_2208_, 1);
v_v_2215_ = lean_ctor_get(v_r_2208_, 2);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_r_2208_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2230_ = lean_ctor_get(v_r_2208_, 4);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_r_2208_, 3);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_r_2208_, 0);
lean_dec(v_unused_2232_);
v___x_2217_ = v_r_2208_;
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_v_2215_);
lean_inc(v_k_2214_);
lean_dec(v_r_2208_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_unsigned_to_nat(3u);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 4, v_l_2191_);
lean_ctor_set(v___x_2217_, 3, v_l_2191_);
lean_ctor_set(v___x_2217_, 2, v_v_2210_);
lean_ctor_set(v___x_2217_, 1, v_k_2209_);
lean_ctor_set(v___x_2217_, 0, v___x_2105_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2209_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2210_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_l_2191_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_l_2191_);
v___x_2221_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2223_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 4, v_l_2191_);
lean_ctor_set(v___x_2212_, 2, v_v_1958_);
lean_ctor_set(v___x_2212_, 1, v_k_1957_);
lean_ctor_set(v___x_2212_, 0, v___x_2105_);
v___x_2223_ = v___x_2212_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_l_2191_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_l_2191_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v___x_2223_);
lean_ctor_set(v___x_1962_, 3, v___x_2221_);
lean_ctor_set(v___x_1962_, 2, v_v_2215_);
lean_ctor_set(v___x_1962_, 1, v_k_2214_);
lean_ctor_set(v___x_1962_, 0, v___x_2219_);
v___x_2225_ = v___x_1962_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2214_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2215_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_unsigned_to_nat(2u);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_r_2208_);
lean_ctor_set(v___x_1962_, 3, v_impl_2104_);
lean_ctor_set(v___x_1962_, 0, v___x_2237_);
v___x_2239_ = v___x_1962_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_impl_2104_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_r_2208_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v_k_1953_);
lean_ctor_set(v___x_2243_, 2, v_v_1954_);
lean_ctor_set(v___x_2243_, 3, v_t_1955_);
lean_ctor_set(v___x_2243_, 4, v_t_1955_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(lean_object* v_y_2244_, lean_object* v_x_2245_, size_t v_x_2246_, size_t v_x_2247_){
_start:
{
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_object* v_cs_2248_; size_t v_j_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_cs_2248_ = lean_ctor_get(v_x_2245_, 0);
v_j_2249_ = lean_usize_shift_right(v_x_2246_, v_x_2247_);
v___x_2250_ = lean_usize_to_nat(v_j_2249_);
v___x_2251_ = lean_array_get_size(v_cs_2248_);
v___x_2252_ = lean_nat_dec_lt(v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec(v___x_2250_);
lean_dec(v_y_2244_);
return v_x_2245_;
}
else
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2270_; 
lean_inc_ref(v_cs_2248_);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_x_2245_, 0);
lean_dec(v_unused_2271_);
v___x_2254_ = v_x_2245_;
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v_x_2245_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2270_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
size_t v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; size_t v_i_2259_; size_t v___x_2260_; size_t v_shift_2261_; lean_object* v_v_2262_; lean_object* v___x_2263_; lean_object* v_xs_x27_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2256_ = ((size_t)1ULL);
v___x_2257_ = lean_usize_shift_left(v___x_2256_, v_x_2247_);
v___x_2258_ = lean_usize_sub(v___x_2257_, v___x_2256_);
v_i_2259_ = lean_usize_land(v_x_2246_, v___x_2258_);
v___x_2260_ = ((size_t)5ULL);
v_shift_2261_ = lean_usize_sub(v_x_2247_, v___x_2260_);
v_v_2262_ = lean_array_fget(v_cs_2248_, v___x_2250_);
v___x_2263_ = lean_box(0);
v_xs_x27_2264_ = lean_array_fset(v_cs_2248_, v___x_2250_, v___x_2263_);
v___x_2265_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2244_, v_v_2262_, v_i_2259_, v_shift_2261_);
v___x_2266_ = lean_array_fset(v_xs_x27_2264_, v___x_2250_, v___x_2265_);
lean_dec(v___x_2250_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2266_);
v___x_2268_ = v___x_2254_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_vs_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_vs_2272_ = lean_ctor_get(v_x_2245_, 0);
v___x_2273_ = lean_usize_to_nat(v_x_2246_);
v___x_2274_ = lean_array_get_size(v_vs_2272_);
v___x_2275_ = lean_nat_dec_lt(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec(v___x_2273_);
lean_dec(v_y_2244_);
return v_x_2245_;
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2290_; 
lean_inc_ref(v_vs_2272_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2245_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v_x_2245_, 0);
lean_dec(v_unused_2291_);
v___x_2277_ = v_x_2245_;
v_isShared_2278_ = v_isSharedCheck_2290_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2245_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2290_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_v_2279_; lean_object* v___x_2280_; lean_object* v_xs_x27_2281_; lean_object* v___y_2283_; uint8_t v___x_2288_; 
v_v_2279_ = lean_array_fget(v_vs_2272_, v___x_2273_);
v___x_2280_ = lean_box(0);
v_xs_x27_2281_ = lean_array_fset(v_vs_2272_, v___x_2273_, v___x_2280_);
v___x_2288_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2244_, v_v_2279_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2244_, v___x_2280_, v_v_2279_);
v___y_2283_ = v___x_2289_;
goto v___jp_2282_;
}
else
{
lean_dec(v_y_2244_);
v___y_2283_ = v_v_2279_;
goto v___jp_2282_;
}
v___jp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_array_fset(v_xs_x27_2281_, v___x_2273_, v___y_2283_);
lean_dec(v___x_2273_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2284_);
v___x_2286_ = v___x_2277_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg___boxed(lean_object* v_y_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
size_t v_x_6046__boxed_2296_; size_t v_x_6047__boxed_2297_; lean_object* v_res_2298_; 
v_x_6046__boxed_2296_ = lean_unbox_usize(v_x_2294_);
lean_dec(v_x_2294_);
v_x_6047__boxed_2297_ = lean_unbox_usize(v_x_2295_);
lean_dec(v_x_2295_);
v_res_2298_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2292_, v_x_2293_, v_x_6046__boxed_2296_, v_x_6047__boxed_2297_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2299_, lean_object* v_inst_2300_, lean_object* v_t_2301_, lean_object* v_i_2302_){
_start:
{
lean_object* v_root_2303_; lean_object* v_tail_2304_; lean_object* v_size_2305_; size_t v_shift_2306_; lean_object* v_tailOff_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2334_; 
v_root_2303_ = lean_ctor_get(v_t_2301_, 0);
v_tail_2304_ = lean_ctor_get(v_t_2301_, 1);
v_size_2305_ = lean_ctor_get(v_t_2301_, 2);
v_shift_2306_ = lean_ctor_get_usize(v_t_2301_, 4);
v_tailOff_2307_ = lean_ctor_get(v_t_2301_, 3);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_t_2301_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2309_ = v_t_2301_;
v_isShared_2310_ = v_isSharedCheck_2334_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_tailOff_2307_);
lean_inc(v_size_2305_);
lean_inc(v_tail_2304_);
lean_inc(v_root_2303_);
lean_dec(v_t_2301_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2334_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_le(v_tailOff_2307_, v_i_2302_);
if (v___x_2311_ == 0)
{
size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2312_ = lean_usize_of_nat(v_i_2302_);
v___x_2313_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2299_, v_root_2303_, v___x_2312_, v_shift_2306_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2313_);
v___x_2315_ = v___x_2309_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_tail_2304_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_size_2305_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_tailOff_2307_);
lean_ctor_set_usize(v_reuseFailAlloc_2316_, 4, v_shift_2306_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = lean_nat_sub(v_i_2302_, v_tailOff_2307_);
v___x_2318_ = lean_array_get_size(v_tail_2304_);
v___x_2319_ = lean_nat_dec_lt(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2321_; 
lean_dec(v___x_2317_);
lean_dec(v_y_2299_);
if (v_isShared_2310_ == 0)
{
v___x_2321_ = v___x_2309_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_root_2303_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_tail_2304_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_size_2305_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_tailOff_2307_);
lean_ctor_set_usize(v_reuseFailAlloc_2322_, 4, v_shift_2306_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
else
{
lean_object* v_v_2323_; lean_object* v___x_2324_; lean_object* v_xs_x27_2325_; lean_object* v___y_2327_; uint8_t v___x_2332_; 
v_v_2323_ = lean_array_fget(v_tail_2304_, v___x_2317_);
v___x_2324_ = lean_box(0);
v_xs_x27_2325_ = lean_array_fset(v_tail_2304_, v___x_2317_, v___x_2324_);
v___x_2332_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2299_, v_v_2323_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2299_, v___x_2324_, v_v_2323_);
v___y_2327_ = v___x_2333_;
goto v___jp_2326_;
}
else
{
lean_dec(v_y_2299_);
v___y_2327_ = v_v_2323_;
goto v___jp_2326_;
}
v___jp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = lean_array_fset(v_xs_x27_2325_, v___x_2317_, v___y_2327_);
lean_dec(v___x_2317_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2328_);
v___x_2330_ = v___x_2309_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_root_2303_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_size_2305_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_tailOff_2307_);
lean_ctor_set_usize(v_reuseFailAlloc_2331_, 4, v_shift_2306_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2335_, lean_object* v_inst_2336_, lean_object* v_t_2337_, lean_object* v_i_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2335_, v_inst_2336_, v_t_2337_, v_i_2338_);
lean_dec(v_i_2338_);
lean_dec(v_inst_2336_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2340_, lean_object* v_y_2341_, lean_object* v_x_2342_, lean_object* v_s_2343_){
_start:
{
lean_object* v_structs_2344_; lean_object* v_typeIdOf_2345_; lean_object* v_exprToStructId_2346_; lean_object* v_exprToStructIdEntries_2347_; lean_object* v_forbiddenNatModules_2348_; lean_object* v_natStructs_2349_; lean_object* v_natTypeIdOf_2350_; lean_object* v_exprToNatStructId_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_structs_2344_ = lean_ctor_get(v_s_2343_, 0);
v_typeIdOf_2345_ = lean_ctor_get(v_s_2343_, 1);
v_exprToStructId_2346_ = lean_ctor_get(v_s_2343_, 2);
v_exprToStructIdEntries_2347_ = lean_ctor_get(v_s_2343_, 3);
v_forbiddenNatModules_2348_ = lean_ctor_get(v_s_2343_, 4);
v_natStructs_2349_ = lean_ctor_get(v_s_2343_, 5);
v_natTypeIdOf_2350_ = lean_ctor_get(v_s_2343_, 6);
v_exprToNatStructId_2351_ = lean_ctor_get(v_s_2343_, 7);
v___x_2352_ = lean_array_get_size(v_structs_2344_);
v___x_2353_ = lean_nat_dec_lt(v_a_2340_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec(v_y_2341_);
return v_s_2343_;
}
else
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2416_; 
lean_inc_ref(v_exprToNatStructId_2351_);
lean_inc_ref(v_natTypeIdOf_2350_);
lean_inc_ref(v_natStructs_2349_);
lean_inc_ref(v_forbiddenNatModules_2348_);
lean_inc_ref(v_exprToStructIdEntries_2347_);
lean_inc_ref(v_exprToStructId_2346_);
lean_inc_ref(v_typeIdOf_2345_);
lean_inc_ref(v_structs_2344_);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_s_2343_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2417_ = lean_ctor_get(v_s_2343_, 7);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2343_, 6);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2343_, 5);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2343_, 4);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_s_2343_, 3);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_s_2343_, 2);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_s_2343_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_s_2343_, 0);
lean_dec(v_unused_2424_);
v___x_2355_ = v_s_2343_;
v_isShared_2356_ = v_isSharedCheck_2416_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v_s_2343_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2416_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_v_2357_; lean_object* v_id_2358_; lean_object* v_ringId_x3f_2359_; lean_object* v_type_2360_; lean_object* v_u_2361_; lean_object* v_intModuleInst_2362_; lean_object* v_leInst_x3f_2363_; lean_object* v_ltInst_x3f_2364_; lean_object* v_lawfulOrderLTInst_x3f_2365_; lean_object* v_isPreorderInst_x3f_2366_; lean_object* v_orderedAddInst_x3f_2367_; lean_object* v_isLinearInst_x3f_2368_; lean_object* v_noNatDivInst_x3f_2369_; lean_object* v_ringInst_x3f_2370_; lean_object* v_commRingInst_x3f_2371_; lean_object* v_orderedRingInst_x3f_2372_; lean_object* v_fieldInst_x3f_2373_; lean_object* v_charInst_x3f_2374_; lean_object* v_zero_2375_; lean_object* v_ofNatZero_2376_; lean_object* v_one_x3f_2377_; lean_object* v_leFn_x3f_2378_; lean_object* v_ltFn_x3f_2379_; lean_object* v_addFn_2380_; lean_object* v_zsmulFn_2381_; lean_object* v_nsmulFn_2382_; lean_object* v_zsmulFn_x3f_2383_; lean_object* v_nsmulFn_x3f_2384_; lean_object* v_homomulFn_x3f_2385_; lean_object* v_subFn_2386_; lean_object* v_negFn_2387_; lean_object* v_vars_2388_; lean_object* v_varMap_2389_; lean_object* v_lowers_2390_; lean_object* v_uppers_2391_; lean_object* v_diseqs_2392_; lean_object* v_assignment_2393_; uint8_t v_caseSplits_2394_; lean_object* v_conflict_x3f_2395_; lean_object* v_diseqSplits_2396_; lean_object* v_elimEqs_2397_; lean_object* v_elimStack_2398_; lean_object* v_occurs_2399_; lean_object* v_ignored_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2415_; 
v_v_2357_ = lean_array_fget(v_structs_2344_, v_a_2340_);
v_id_2358_ = lean_ctor_get(v_v_2357_, 0);
v_ringId_x3f_2359_ = lean_ctor_get(v_v_2357_, 1);
v_type_2360_ = lean_ctor_get(v_v_2357_, 2);
v_u_2361_ = lean_ctor_get(v_v_2357_, 3);
v_intModuleInst_2362_ = lean_ctor_get(v_v_2357_, 4);
v_leInst_x3f_2363_ = lean_ctor_get(v_v_2357_, 5);
v_ltInst_x3f_2364_ = lean_ctor_get(v_v_2357_, 6);
v_lawfulOrderLTInst_x3f_2365_ = lean_ctor_get(v_v_2357_, 7);
v_isPreorderInst_x3f_2366_ = lean_ctor_get(v_v_2357_, 8);
v_orderedAddInst_x3f_2367_ = lean_ctor_get(v_v_2357_, 9);
v_isLinearInst_x3f_2368_ = lean_ctor_get(v_v_2357_, 10);
v_noNatDivInst_x3f_2369_ = lean_ctor_get(v_v_2357_, 11);
v_ringInst_x3f_2370_ = lean_ctor_get(v_v_2357_, 12);
v_commRingInst_x3f_2371_ = lean_ctor_get(v_v_2357_, 13);
v_orderedRingInst_x3f_2372_ = lean_ctor_get(v_v_2357_, 14);
v_fieldInst_x3f_2373_ = lean_ctor_get(v_v_2357_, 15);
v_charInst_x3f_2374_ = lean_ctor_get(v_v_2357_, 16);
v_zero_2375_ = lean_ctor_get(v_v_2357_, 17);
v_ofNatZero_2376_ = lean_ctor_get(v_v_2357_, 18);
v_one_x3f_2377_ = lean_ctor_get(v_v_2357_, 19);
v_leFn_x3f_2378_ = lean_ctor_get(v_v_2357_, 20);
v_ltFn_x3f_2379_ = lean_ctor_get(v_v_2357_, 21);
v_addFn_2380_ = lean_ctor_get(v_v_2357_, 22);
v_zsmulFn_2381_ = lean_ctor_get(v_v_2357_, 23);
v_nsmulFn_2382_ = lean_ctor_get(v_v_2357_, 24);
v_zsmulFn_x3f_2383_ = lean_ctor_get(v_v_2357_, 25);
v_nsmulFn_x3f_2384_ = lean_ctor_get(v_v_2357_, 26);
v_homomulFn_x3f_2385_ = lean_ctor_get(v_v_2357_, 27);
v_subFn_2386_ = lean_ctor_get(v_v_2357_, 28);
v_negFn_2387_ = lean_ctor_get(v_v_2357_, 29);
v_vars_2388_ = lean_ctor_get(v_v_2357_, 30);
v_varMap_2389_ = lean_ctor_get(v_v_2357_, 31);
v_lowers_2390_ = lean_ctor_get(v_v_2357_, 32);
v_uppers_2391_ = lean_ctor_get(v_v_2357_, 33);
v_diseqs_2392_ = lean_ctor_get(v_v_2357_, 34);
v_assignment_2393_ = lean_ctor_get(v_v_2357_, 35);
v_caseSplits_2394_ = lean_ctor_get_uint8(v_v_2357_, sizeof(void*)*42);
v_conflict_x3f_2395_ = lean_ctor_get(v_v_2357_, 36);
v_diseqSplits_2396_ = lean_ctor_get(v_v_2357_, 37);
v_elimEqs_2397_ = lean_ctor_get(v_v_2357_, 38);
v_elimStack_2398_ = lean_ctor_get(v_v_2357_, 39);
v_occurs_2399_ = lean_ctor_get(v_v_2357_, 40);
v_ignored_2400_ = lean_ctor_get(v_v_2357_, 41);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_v_2357_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2402_ = v_v_2357_;
v_isShared_2403_ = v_isSharedCheck_2415_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_ignored_2400_);
lean_inc(v_occurs_2399_);
lean_inc(v_elimStack_2398_);
lean_inc(v_elimEqs_2397_);
lean_inc(v_diseqSplits_2396_);
lean_inc(v_conflict_x3f_2395_);
lean_inc(v_assignment_2393_);
lean_inc(v_diseqs_2392_);
lean_inc(v_uppers_2391_);
lean_inc(v_lowers_2390_);
lean_inc(v_varMap_2389_);
lean_inc(v_vars_2388_);
lean_inc(v_negFn_2387_);
lean_inc(v_subFn_2386_);
lean_inc(v_homomulFn_x3f_2385_);
lean_inc(v_nsmulFn_x3f_2384_);
lean_inc(v_zsmulFn_x3f_2383_);
lean_inc(v_nsmulFn_2382_);
lean_inc(v_zsmulFn_2381_);
lean_inc(v_addFn_2380_);
lean_inc(v_ltFn_x3f_2379_);
lean_inc(v_leFn_x3f_2378_);
lean_inc(v_one_x3f_2377_);
lean_inc(v_ofNatZero_2376_);
lean_inc(v_zero_2375_);
lean_inc(v_charInst_x3f_2374_);
lean_inc(v_fieldInst_x3f_2373_);
lean_inc(v_orderedRingInst_x3f_2372_);
lean_inc(v_commRingInst_x3f_2371_);
lean_inc(v_ringInst_x3f_2370_);
lean_inc(v_noNatDivInst_x3f_2369_);
lean_inc(v_isLinearInst_x3f_2368_);
lean_inc(v_orderedAddInst_x3f_2367_);
lean_inc(v_isPreorderInst_x3f_2366_);
lean_inc(v_lawfulOrderLTInst_x3f_2365_);
lean_inc(v_ltInst_x3f_2364_);
lean_inc(v_leInst_x3f_2363_);
lean_inc(v_intModuleInst_2362_);
lean_inc(v_u_2361_);
lean_inc(v_type_2360_);
lean_inc(v_ringId_x3f_2359_);
lean_inc(v_id_2358_);
lean_dec(v_v_2357_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2415_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v_xs_x27_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2404_ = lean_box(0);
v_xs_x27_2405_ = lean_array_fset(v_structs_2344_, v_a_2340_, v___x_2404_);
v___x_2406_ = lean_box(1);
v___x_2407_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2341_, v___x_2406_, v_occurs_2399_, v_x_2342_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 40, v___x_2407_);
v___x_2409_ = v___x_2402_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_id_2358_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_ringId_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_type_2360_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_u_2361_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_intModuleInst_2362_);
lean_ctor_set(v_reuseFailAlloc_2414_, 5, v_leInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2414_, 6, v_ltInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2414_, 7, v_lawfulOrderLTInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2414_, 8, v_isPreorderInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2414_, 9, v_orderedAddInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2414_, 10, v_isLinearInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2414_, 11, v_noNatDivInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2414_, 12, v_ringInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2414_, 13, v_commRingInst_x3f_2371_);
lean_ctor_set(v_reuseFailAlloc_2414_, 14, v_orderedRingInst_x3f_2372_);
lean_ctor_set(v_reuseFailAlloc_2414_, 15, v_fieldInst_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2414_, 16, v_charInst_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2414_, 17, v_zero_2375_);
lean_ctor_set(v_reuseFailAlloc_2414_, 18, v_ofNatZero_2376_);
lean_ctor_set(v_reuseFailAlloc_2414_, 19, v_one_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2414_, 20, v_leFn_x3f_2378_);
lean_ctor_set(v_reuseFailAlloc_2414_, 21, v_ltFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2414_, 22, v_addFn_2380_);
lean_ctor_set(v_reuseFailAlloc_2414_, 23, v_zsmulFn_2381_);
lean_ctor_set(v_reuseFailAlloc_2414_, 24, v_nsmulFn_2382_);
lean_ctor_set(v_reuseFailAlloc_2414_, 25, v_zsmulFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2414_, 26, v_nsmulFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2414_, 27, v_homomulFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2414_, 28, v_subFn_2386_);
lean_ctor_set(v_reuseFailAlloc_2414_, 29, v_negFn_2387_);
lean_ctor_set(v_reuseFailAlloc_2414_, 30, v_vars_2388_);
lean_ctor_set(v_reuseFailAlloc_2414_, 31, v_varMap_2389_);
lean_ctor_set(v_reuseFailAlloc_2414_, 32, v_lowers_2390_);
lean_ctor_set(v_reuseFailAlloc_2414_, 33, v_uppers_2391_);
lean_ctor_set(v_reuseFailAlloc_2414_, 34, v_diseqs_2392_);
lean_ctor_set(v_reuseFailAlloc_2414_, 35, v_assignment_2393_);
lean_ctor_set(v_reuseFailAlloc_2414_, 36, v_conflict_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2414_, 37, v_diseqSplits_2396_);
lean_ctor_set(v_reuseFailAlloc_2414_, 38, v_elimEqs_2397_);
lean_ctor_set(v_reuseFailAlloc_2414_, 39, v_elimStack_2398_);
lean_ctor_set(v_reuseFailAlloc_2414_, 40, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2414_, 41, v_ignored_2400_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*42, v_caseSplits_2394_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = lean_array_fset(v_xs_x27_2405_, v_a_2340_, v___x_2409_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2410_);
v___x_2412_ = v___x_2355_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_typeIdOf_2345_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v_exprToStructId_2346_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v_exprToStructIdEntries_2347_);
lean_ctor_set(v_reuseFailAlloc_2413_, 4, v_forbiddenNatModules_2348_);
lean_ctor_set(v_reuseFailAlloc_2413_, 5, v_natStructs_2349_);
lean_ctor_set(v_reuseFailAlloc_2413_, 6, v_natTypeIdOf_2350_);
lean_ctor_set(v_reuseFailAlloc_2413_, 7, v_exprToNatStructId_2351_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2425_, lean_object* v_y_2426_, lean_object* v_x_2427_, lean_object* v_s_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2425_, v_y_2426_, v_x_2427_, v_s_2428_);
lean_dec(v_x_2427_);
lean_dec(v_a_2425_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2430_, lean_object* v_y_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2430_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2457_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2457_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
uint8_t v___x_2449_; 
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2431_, v_a_2445_);
lean_dec(v_a_2445_);
if (v___x_2449_ == 0)
{
lean_object* v___f_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_del_object(v___x_2447_);
lean_inc(v_a_2432_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2450_, 0, v_a_2432_);
lean_closure_set(v___f_2450_, 1, v_y_2431_);
lean_closure_set(v___f_2450_, 2, v_x_2430_);
v___x_2451_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2452_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2451_, v___f_2450_, v_a_2433_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_y_2431_);
lean_dec(v_x_2430_);
v___x_2453_ = lean_box(0);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2453_);
v___x_2455_ = v___x_2447_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_y_2431_);
lean_dec(v_x_2430_);
v_a_2458_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2444_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2444_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2466_, lean_object* v_y_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2466_, v_y_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec(v_a_2468_);
return v_res_2480_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2481_, lean_object* v_k_2482_, lean_object* v_t_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2482_, v_t_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2485_, lean_object* v_k_2486_, lean_object* v_t_2487_){
_start:
{
uint8_t v_res_2488_; lean_object* v_r_2489_; 
v_res_2488_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2485_, v_k_2486_, v_t_2487_);
lean_dec(v_t_2487_);
lean_dec(v_k_2486_);
v_r_2489_ = lean_box(v_res_2488_);
return v_r_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2490_, lean_object* v_k_2491_, lean_object* v_v_2492_, lean_object* v_t_2493_, lean_object* v_hl_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2491_, v_v_2492_, v_t_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2496_, lean_object* v_inst_2497_, lean_object* v_x_2498_, size_t v_x_2499_, size_t v_x_2500_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2496_, v_x_2498_, v_x_2499_, v_x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2502_, lean_object* v_inst_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v_x_2506_){
_start:
{
size_t v_x_6290__boxed_2507_; size_t v_x_6291__boxed_2508_; lean_object* v_res_2509_; 
v_x_6290__boxed_2507_ = lean_unbox_usize(v_x_2505_);
lean_dec(v_x_2505_);
v_x_6291__boxed_2508_ = lean_unbox_usize(v_x_2506_);
lean_dec(v_x_2506_);
v_res_2509_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2502_, v_inst_2503_, v_x_2504_, v_x_6290__boxed_2507_, v_x_6291__boxed_2508_);
lean_dec(v_inst_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2510_, lean_object* v_p_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
if (lean_obj_tag(v_p_2511_) == 1)
{
lean_object* v_v_2524_; lean_object* v_p_2525_; lean_object* v___x_2526_; 
v_v_2524_ = lean_ctor_get(v_p_2511_, 1);
lean_inc(v_v_2524_);
v_p_2525_ = lean_ctor_get(v_p_2511_, 2);
lean_inc(v_p_2525_);
lean_dec_ref(v_p_2511_);
lean_inc(v_y_2510_);
v___x_2526_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2524_, v_y_2510_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_dec_ref(v___x_2526_);
v_p_2511_ = v_p_2525_;
goto _start;
}
else
{
lean_dec(v_p_2525_);
lean_dec(v_y_2510_);
return v___x_2526_;
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_p_2511_);
lean_dec(v_y_2510_);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2530_, lean_object* v_p_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2530_, v_p_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec(v_a_2532_);
return v_res_2544_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
if (lean_obj_tag(v_p_2548_) == 1)
{
lean_object* v_v_2561_; lean_object* v_p_2562_; lean_object* v___x_2563_; 
v_v_2561_ = lean_ctor_get(v_p_2548_, 1);
lean_inc(v_v_2561_);
v_p_2562_ = lean_ctor_get(v_p_2548_, 2);
lean_inc(v_p_2562_);
lean_dec_ref(v_p_2548_);
v___x_2563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2561_, v_p_2562_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_p_2548_);
v___x_2564_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2565_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2564_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
if (lean_obj_tag(v_p_2580_) == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
else
{
lean_object* v_k_2595_; lean_object* v_v_2596_; lean_object* v_p_2597_; lean_object* v___x_2598_; 
v_k_2595_ = lean_ctor_get(v_p_2580_, 0);
v_v_2596_ = lean_ctor_get(v_p_2580_, 1);
v_p_2597_ = lean_ctor_get(v_p_2580_, 2);
v___x_2598_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2625_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2625_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2625_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___y_2604_; lean_object* v_elimEqs_2619_; lean_object* v_size_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_elimEqs_2619_ = lean_ctor_get(v_a_2599_, 38);
lean_inc_ref(v_elimEqs_2619_);
lean_dec(v_a_2599_);
v_size_2620_ = lean_ctor_get(v_elimEqs_2619_, 2);
v___x_2621_ = lean_box(0);
v___x_2622_ = lean_nat_dec_lt(v_v_2596_, v_size_2620_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_dec_ref(v_elimEqs_2619_);
v___x_2623_ = l_outOfBounds___redArg(v___x_2621_);
v___y_2604_ = v___x_2623_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2621_, v_elimEqs_2619_, v_v_2596_);
v___y_2604_ = v___x_2624_;
goto v___jp_2603_;
}
v___jp_2603_:
{
if (lean_obj_tag(v___y_2604_) == 1)
{
lean_object* v_val_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2617_; 
v_val_2605_ = lean_ctor_get(v___y_2604_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___y_2604_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2607_ = v___y_2604_;
v_isShared_2608_ = v_isSharedCheck_2617_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_val_2605_);
lean_dec(v___y_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2617_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
lean_inc(v_v_2596_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_v_2596_);
lean_ctor_set(v___x_2609_, 1, v_val_2605_);
lean_inc(v_k_2595_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_k_2595_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2610_);
v___x_2612_ = v___x_2607_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2612_);
v___x_2614_ = v___x_2601_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_dec(v___y_2604_);
lean_del_object(v___x_2601_);
v_p_2580_ = v_p_2597_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2598_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2598_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec(v_p_2634_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 0)
{
return v_x_2649_;
}
else
{
lean_object* v_k_2650_; lean_object* v_p_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_k_2650_ = lean_ctor_get(v_x_2648_, 0);
v_p_2651_ = lean_ctor_get(v_x_2648_, 2);
v___x_2652_ = lean_nat_to_int(v_x_2649_);
v___x_2653_ = l_Int_gcd(v_k_2650_, v___x_2652_);
lean_dec(v___x_2652_);
v_x_2648_ = v_p_2651_;
v_x_2649_ = v___x_2653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2655_, v_x_2656_);
lean_dec(v_x_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2658_){
_start:
{
if (lean_obj_tag(v_p_2658_) == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_unsigned_to_nat(1u);
return v___x_2659_;
}
else
{
lean_object* v_k_2660_; lean_object* v_p_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v_k_2660_ = lean_ctor_get(v_p_2658_, 0);
v_p_2661_ = lean_ctor_get(v_p_2658_, 2);
v___x_2662_ = lean_nat_abs(v_k_2660_);
v___x_2663_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2661_, v___x_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2664_);
lean_dec(v_p_2664_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2666_, lean_object* v_k_2667_){
_start:
{
if (lean_obj_tag(v_p_2666_) == 0)
{
return v_p_2666_;
}
else
{
lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v_p_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
v_k_2668_ = lean_ctor_get(v_p_2666_, 0);
v_v_2669_ = lean_ctor_get(v_p_2666_, 1);
v_p_2670_ = lean_ctor_get(v_p_2666_, 2);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_p_2666_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v_p_2666_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_p_2670_);
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
lean_dec(v_p_2666_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_int_ediv(v_k_2668_, v_k_2667_);
lean_dec(v_k_2668_);
v___x_2675_ = l_Lean_Grind_Linarith_Poly_div(v_p_2670_, v_k_2667_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 2, v___x_2675_);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_v_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2680_, lean_object* v_k_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Grind_Linarith_Poly_div(v_p_2680_, v_k_2681_);
lean_dec(v_k_2681_);
return v_res_2682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_to_int(v___x_2683_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2686_ = lean_int_neg(v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2687_, lean_object* v_x_2688_, lean_object* v_p_2689_){
_start:
{
uint8_t v___y_2691_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2703_ = lean_int_dec_eq(v_k_2687_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2705_ = lean_int_dec_eq(v_k_2687_, v___x_2704_);
v___y_2691_ = v___x_2705_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v___x_2703_;
goto v___jp_2690_;
}
v___jp_2690_:
{
if (v___y_2691_ == 0)
{
if (lean_obj_tag(v_p_2689_) == 0)
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_k_2687_);
lean_ctor_set(v___x_2692_, 1, v_x_2688_);
return v___x_2692_;
}
else
{
lean_object* v_k_2693_; lean_object* v_v_2694_; lean_object* v_p_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v_k_2693_ = lean_ctor_get(v_p_2689_, 0);
lean_inc(v_k_2693_);
v_v_2694_ = lean_ctor_get(v_p_2689_, 1);
lean_inc(v_v_2694_);
v_p_2695_ = lean_ctor_get(v_p_2689_, 2);
lean_inc(v_p_2695_);
lean_dec_ref(v_p_2689_);
v___x_2696_ = lean_nat_abs(v_k_2693_);
v___x_2697_ = lean_nat_abs(v_k_2687_);
v___x_2698_ = lean_nat_dec_lt(v___x_2696_, v___x_2697_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
if (v___x_2698_ == 0)
{
lean_dec(v_v_2694_);
lean_dec(v_k_2693_);
v_p_2689_ = v_p_2695_;
goto _start;
}
else
{
lean_dec(v_x_2688_);
lean_dec(v_k_2687_);
v_k_2687_ = v_k_2693_;
v_x_2688_ = v_v_2694_;
v_p_2689_ = v_p_2695_;
goto _start;
}
}
}
else
{
lean_object* v___x_2701_; 
lean_dec(v_p_2689_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_k_2687_);
lean_ctor_set(v___x_2701_, 1, v_x_2688_);
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2706_){
_start:
{
if (lean_obj_tag(v_p_2706_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_box(0);
return v___x_2707_;
}
else
{
lean_object* v_k_2708_; lean_object* v_v_2709_; lean_object* v_p_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_k_2708_ = lean_ctor_get(v_p_2706_, 0);
lean_inc(v_k_2708_);
v_v_2709_ = lean_ctor_get(v_p_2706_, 1);
lean_inc(v_v_2709_);
v_p_2710_ = lean_ctor_get(v_p_2706_, 2);
lean_inc(v_p_2710_);
lean_dec_ref(v_p_2706_);
v___x_2711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2708_, v_v_2709_, v_p_2710_);
v___x_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
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
