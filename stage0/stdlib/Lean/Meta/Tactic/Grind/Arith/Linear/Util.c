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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_es_326_; lean_object* v___x_327_; size_t v___x_328_; size_t v___x_329_; size_t v___x_330_; lean_object* v_j_331_; lean_object* v___x_332_; 
v_es_326_ = lean_ctor_get(v_x_323_, 0);
v___x_327_ = lean_box(2);
v___x_328_ = ((size_t)5ULL);
v___x_329_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_330_ = lean_usize_land(v_x_324_, v___x_329_);
v_j_331_ = lean_usize_to_nat(v___x_330_);
v___x_332_ = lean_array_get_borrowed(v___x_327_, v_es_326_, v_j_331_);
lean_dec(v_j_331_);
switch(lean_obj_tag(v___x_332_))
{
case 0:
{
lean_object* v_key_333_; lean_object* v_val_334_; uint8_t v___x_335_; 
v_key_333_ = lean_ctor_get(v___x_332_, 0);
v_val_334_ = lean_ctor_get(v___x_332_, 1);
v___x_335_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_325_, v_key_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
lean_inc(v_val_334_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_val_334_);
return v___x_337_;
}
}
case 1:
{
lean_object* v_node_338_; size_t v___x_339_; 
v_node_338_ = lean_ctor_get(v___x_332_, 0);
v___x_339_ = lean_usize_shift_right(v_x_324_, v___x_328_);
v_x_323_ = v_node_338_;
v_x_324_ = v___x_339_;
goto _start;
}
default: 
{
lean_object* v___x_341_; 
v___x_341_ = lean_box(0);
return v___x_341_;
}
}
}
else
{
lean_object* v_ks_342_; lean_object* v_vs_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_ks_342_ = lean_ctor_get(v_x_323_, 0);
v_vs_343_ = lean_ctor_get(v_x_323_, 1);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_342_, v_vs_343_, v___x_344_, v_x_325_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
size_t v_x_867__boxed_349_; lean_object* v_res_350_; 
v_x_867__boxed_349_ = lean_unbox_usize(v_x_347_);
lean_dec(v_x_347_);
v_res_350_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_346_, v_x_867__boxed_349_, v_x_348_);
lean_dec_ref(v_x_348_);
lean_dec_ref(v_x_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint64_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_352_);
v___x_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_351_, v___x_354_, v_x_352_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_356_, v_x_357_);
lean_dec_ref(v_x_357_);
lean_dec_ref(v_x_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_exprToStructId_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v_exprToStructId_368_ = lean_ctor_get(v_a_364_, 2);
lean_inc_ref(v_exprToStructId_368_);
lean_dec(v_a_364_);
v___x_369_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_368_, v_e_359_);
lean_dec_ref(v_exprToStructId_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_363_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_363_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_382_, v_a_383_, v_a_384_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_e_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_387_, v_a_388_, v_a_396_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_e_400_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_414_, v_x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_417_, v_x_418_, v_x_419_);
lean_dec_ref(v_x_419_);
lean_dec_ref(v_x_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_421_, lean_object* v_x_422_, size_t v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_422_, v_x_423_, v_x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_984__boxed_430_; lean_object* v_res_431_; 
v_x_984__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_426_, v_x_427_, v_x_984__boxed_430_, v_x_429_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_427_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_432_, lean_object* v_keys_433_, lean_object* v_vals_434_, lean_object* v_heq_435_, lean_object* v_i_436_, lean_object* v_k_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_433_, v_vals_434_, v_i_436_, v_k_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_439_, lean_object* v_keys_440_, lean_object* v_vals_441_, lean_object* v_heq_442_, lean_object* v_i_443_, lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_439_, v_keys_440_, v_vals_441_, v_heq_442_, v_i_443_, v_k_444_);
lean_dec_ref(v_k_444_);
lean_dec_ref(v_vals_441_);
lean_dec_ref(v_keys_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_ks_450_; lean_object* v_vs_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_475_; 
v_ks_450_ = lean_ctor_get(v_x_446_, 0);
v_vs_451_ = lean_ctor_get(v_x_446_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_475_ == 0)
{
v___x_453_ = v_x_446_;
v_isShared_454_ = v_isSharedCheck_475_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_vs_451_);
lean_inc(v_ks_450_);
lean_dec(v_x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_475_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_ks_450_);
v___x_456_ = lean_nat_dec_lt(v_x_447_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_x_447_);
v___x_457_ = lean_array_push(v_ks_450_, v_x_448_);
v___x_458_ = lean_array_push(v_vs_451_, v_x_449_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_458_);
lean_ctor_set(v___x_453_, 0, v___x_457_);
v___x_460_ = v___x_453_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
else
{
lean_object* v_k_x27_462_; uint8_t v___x_463_; 
v_k_x27_462_ = lean_array_fget_borrowed(v_ks_450_, v_x_447_);
v___x_463_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_448_, v_k_x27_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_465_; 
if (v_isShared_454_ == 0)
{
v___x_465_ = v___x_453_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ks_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_vs_451_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_x_447_, v___x_466_);
lean_dec(v_x_447_);
v_x_446_ = v___x_465_;
v_x_447_ = v___x_467_;
goto _start;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_array_fset(v_ks_450_, v_x_447_, v_x_448_);
v___x_471_ = lean_array_fset(v_vs_451_, v_x_447_, v_x_449_);
lean_dec(v_x_447_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_471_);
lean_ctor_set(v___x_453_, 0, v___x_470_);
v___x_473_ = v___x_453_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_476_, lean_object* v_k_477_, lean_object* v_v_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_476_, v___x_479_, v_k_477_, v_v_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_482_, size_t v_x_483_, size_t v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_es_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v_j_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_es_487_ = lean_ctor_get(v_x_482_, 0);
v___x_488_ = ((size_t)5ULL);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_491_ = lean_usize_land(v_x_483_, v___x_490_);
v_j_492_ = lean_usize_to_nat(v___x_491_);
v___x_493_ = lean_array_get_size(v_es_487_);
v___x_494_ = lean_nat_dec_lt(v_j_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_j_492_);
lean_dec(v_x_486_);
lean_dec_ref(v_x_485_);
return v_x_482_;
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_es_487_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_532_);
v___x_496_ = v_x_482_;
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_531_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_v_498_; lean_object* v___x_499_; lean_object* v_xs_x27_500_; lean_object* v___y_502_; 
v_v_498_ = lean_array_fget(v_es_487_, v_j_492_);
v___x_499_ = lean_box(0);
v_xs_x27_500_ = lean_array_fset(v_es_487_, v_j_492_, v___x_499_);
switch(lean_obj_tag(v_v_498_))
{
case 0:
{
lean_object* v_key_507_; lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_key_507_ = lean_ctor_get(v_v_498_, 0);
v_val_508_ = lean_ctor_get(v_v_498_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_v_498_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_inc(v_key_507_);
lean_dec(v_v_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_485_, v_key_507_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_510_);
v___x_513_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_507_, v_val_508_, v_x_485_, v_x_486_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___y_502_ = v___x_514_;
goto v___jp_501_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_val_508_);
lean_dec(v_key_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_x_486_);
lean_ctor_set(v___x_510_, 0, v_x_485_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_x_485_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_x_486_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_502_ = v___x_516_;
goto v___jp_501_;
}
}
}
}
case 1:
{
lean_object* v_node_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_node_519_ = lean_ctor_get(v_v_498_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v_v_498_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_node_519_);
lean_dec(v_v_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = lean_usize_shift_right(v_x_483_, v___x_488_);
v___x_524_ = lean_usize_add(v_x_484_, v___x_489_);
v___x_525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_519_, v___x_523_, v___x_524_, v_x_485_, v_x_486_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v___y_502_ = v___x_527_;
goto v___jp_501_;
}
}
}
default: 
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_x_485_);
lean_ctor_set(v___x_530_, 1, v_x_486_);
v___y_502_ = v___x_530_;
goto v___jp_501_;
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_array_fset(v_xs_x27_500_, v_j_492_, v___y_502_);
lean_dec(v_j_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_533_; lean_object* v_vs_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_554_; 
v_ks_533_ = lean_ctor_get(v_x_482_, 0);
v_vs_534_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_554_ == 0)
{
v___x_536_ = v_x_482_;
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_vs_534_);
lean_inc(v_ks_533_);
lean_dec(v_x_482_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_554_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_ks_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vs_534_);
v___x_539_ = v_reuseFailAlloc_553_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v_newNode_540_; uint8_t v___y_542_; size_t v___x_548_; uint8_t v___x_549_; 
v_newNode_540_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_539_, v_x_485_, v_x_486_);
v___x_548_ = ((size_t)7ULL);
v___x_549_ = lean_usize_dec_le(v___x_548_, v_x_484_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_540_);
v___x_551_ = lean_unsigned_to_nat(4u);
v___x_552_ = lean_nat_dec_lt(v___x_550_, v___x_551_);
lean_dec(v___x_550_);
v___y_542_ = v___x_552_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___x_549_;
goto v___jp_541_;
}
v___jp_541_:
{
if (v___y_542_ == 0)
{
lean_object* v_ks_543_; lean_object* v_vs_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_ks_543_ = lean_ctor_get(v_newNode_540_, 0);
lean_inc_ref(v_ks_543_);
v_vs_544_ = lean_ctor_get(v_newNode_540_, 1);
lean_inc_ref(v_vs_544_);
lean_dec_ref(v_newNode_540_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_484_, v_ks_543_, v_vs_544_, v___x_545_, v___x_546_);
lean_dec_ref(v_vs_544_);
lean_dec_ref(v_ks_543_);
return v___x_547_;
}
else
{
return v_newNode_540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_555_, lean_object* v_keys_556_, lean_object* v_vals_557_, lean_object* v_i_558_, lean_object* v_entries_559_){
_start:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_get_size(v_keys_556_);
v___x_561_ = lean_nat_dec_lt(v_i_558_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec(v_i_558_);
return v_entries_559_;
}
else
{
lean_object* v_k_562_; lean_object* v_v_563_; uint64_t v___x_564_; size_t v_h_565_; size_t v___x_566_; lean_object* v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v_h_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_k_562_ = lean_array_fget_borrowed(v_keys_556_, v_i_558_);
v_v_563_ = lean_array_fget_borrowed(v_vals_557_, v_i_558_);
v___x_564_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_562_);
v_h_565_ = lean_uint64_to_usize(v___x_564_);
v___x_566_ = ((size_t)5ULL);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_sub(v_depth_555_, v___x_568_);
v___x_570_ = lean_usize_mul(v___x_566_, v___x_569_);
v_h_571_ = lean_usize_shift_right(v_h_565_, v___x_570_);
v___x_572_ = lean_nat_add(v_i_558_, v___x_567_);
lean_dec(v_i_558_);
lean_inc(v_v_563_);
lean_inc(v_k_562_);
v___x_573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_559_, v_h_571_, v_depth_555_, v_k_562_, v_v_563_);
v_i_558_ = v___x_572_;
v_entries_559_ = v___x_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_575_, lean_object* v_keys_576_, lean_object* v_vals_577_, lean_object* v_i_578_, lean_object* v_entries_579_){
_start:
{
size_t v_depth_boxed_580_; lean_object* v_res_581_; 
v_depth_boxed_580_ = lean_unbox_usize(v_depth_575_);
lean_dec(v_depth_575_);
v_res_581_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_580_, v_keys_576_, v_vals_577_, v_i_578_, v_entries_579_);
lean_dec_ref(v_vals_577_);
lean_dec_ref(v_keys_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
size_t v_x_7030__boxed_587_; size_t v_x_7031__boxed_588_; lean_object* v_res_589_; 
v_x_7030__boxed_587_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_x_7031__boxed_588_ = lean_unbox_usize(v_x_584_);
lean_dec(v_x_584_);
v_res_589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_582_, v_x_7030__boxed_587_, v_x_7031__boxed_588_, v_x_585_, v_x_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
uint64_t v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___x_593_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_591_);
v___x_594_ = lean_uint64_to_usize(v___x_593_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_590_, v___x_594_, v___x_595_, v_x_591_, v_x_592_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_s_599_){
_start:
{
lean_object* v_structs_600_; lean_object* v_typeIdOf_601_; lean_object* v_exprToStructId_602_; lean_object* v_exprToStructIdEntries_603_; lean_object* v_forbiddenNatModules_604_; lean_object* v_natStructs_605_; lean_object* v_natTypeIdOf_606_; lean_object* v_exprToNatStructId_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
v_structs_600_ = lean_ctor_get(v_s_599_, 0);
v_typeIdOf_601_ = lean_ctor_get(v_s_599_, 1);
v_exprToStructId_602_ = lean_ctor_get(v_s_599_, 2);
v_exprToStructIdEntries_603_ = lean_ctor_get(v_s_599_, 3);
v_forbiddenNatModules_604_ = lean_ctor_get(v_s_599_, 4);
v_natStructs_605_ = lean_ctor_get(v_s_599_, 5);
v_natTypeIdOf_606_ = lean_ctor_get(v_s_599_, 6);
v_exprToNatStructId_607_ = lean_ctor_get(v_s_599_, 7);
v_isSharedCheck_617_ = !lean_is_exclusive(v_s_599_);
if (v_isSharedCheck_617_ == 0)
{
v___x_609_ = v_s_599_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_exprToNatStructId_607_);
lean_inc(v_natTypeIdOf_606_);
lean_inc(v_natStructs_605_);
lean_inc(v_forbiddenNatModules_604_);
lean_inc(v_exprToStructIdEntries_603_);
lean_inc(v_exprToStructId_602_);
lean_inc(v_typeIdOf_601_);
lean_inc(v_structs_600_);
lean_dec(v_s_599_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_inc_n(v_a_598_, 2);
lean_inc_ref(v_e_597_);
v___x_611_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_602_, v_e_597_, v_a_598_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_e_597_);
lean_ctor_set(v___x_612_, 1, v_a_598_);
v___x_613_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_603_, v___x_612_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 3, v___x_613_);
lean_ctor_set(v___x_609_, 2, v___x_611_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_structs_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_typeIdOf_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_forbiddenNatModules_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_natStructs_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_natTypeIdOf_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_exprToNatStructId_607_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_s_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_618_, v_a_619_, v_s_620_);
lean_dec(v_a_619_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_625_, v_a_627_, v_a_632_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
if (lean_obj_tag(v_a_639_) == 1)
{
lean_object* v_val_640_; uint8_t v___x_641_; 
v_val_640_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v_a_639_);
v___x_641_ = lean_nat_dec_eq(v_val_640_, v_a_626_);
lean_dec(v_val_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_628_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; uint8_t v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v___x_644_ = lean_unbox(v_a_643_);
lean_dec(v_a_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_e_625_);
goto v___jp_635_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_646_ = l_Lean_indentExpr(v_e_625_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_Meta_Sym_reportIssue(v___x_647_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_dec_ref(v___x_648_);
goto v___jp_635_;
}
else
{
return v___x_648_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_e_625_);
v_a_649_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_642_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_dec_ref(v_e_625_);
goto v___jp_635_;
}
}
else
{
lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_a_639_);
lean_inc(v_a_626_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_657_, 0, v_e_625_);
lean_closure_set(v___f_657_, 1, v_a_626_);
v___x_658_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_658_, v___f_657_, v_a_627_);
return v___x_659_;
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_e_625_);
v_a_660_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_638_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_638_);
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
v___jp_635_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec(v_a_669_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_679_, v_a_680_, v_a_681_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_708_, v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_712_, lean_object* v_x_713_, size_t v_x_714_, size_t v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_713_, v_x_714_, v_x_715_, v_x_716_, v_x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
size_t v_x_7313__boxed_725_; size_t v_x_7314__boxed_726_; lean_object* v_res_727_; 
v_x_7313__boxed_725_ = lean_unbox_usize(v_x_721_);
lean_dec(v_x_721_);
v_x_7314__boxed_726_ = lean_unbox_usize(v_x_722_);
lean_dec(v_x_722_);
v_res_727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_719_, v_x_720_, v_x_7313__boxed_725_, v_x_7314__boxed_726_, v_x_723_, v_x_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_728_, lean_object* v_n_729_, lean_object* v_k_730_, lean_object* v_v_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_729_, v_k_730_, v_v_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_733_, size_t v_depth_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_entries_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_734_, v_keys_735_, v_vals_736_, v_i_738_, v_entries_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_741_, lean_object* v_depth_742_, lean_object* v_keys_743_, lean_object* v_vals_744_, lean_object* v_heq_745_, lean_object* v_i_746_, lean_object* v_entries_747_){
_start:
{
size_t v_depth_boxed_748_; lean_object* v_res_749_; 
v_depth_boxed_748_ = lean_unbox_usize(v_depth_742_);
lean_dec(v_depth_742_);
v_res_749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_741_, v_depth_boxed_748_, v_keys_743_, v_vals_744_, v_heq_745_, v_i_746_, v_entries_747_);
lean_dec_ref(v_vals_744_);
lean_dec_ref(v_keys_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_751_, v_x_752_, v_x_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v_env_763_; lean_object* v___x_764_; lean_object* v_mctx_765_; lean_object* v_lctx_766_; lean_object* v_options_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_762_ = lean_st_ref_get(v___y_760_);
v_env_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_ref(v_env_763_);
lean_dec(v___x_762_);
v___x_764_ = lean_st_ref_get(v___y_758_);
v_mctx_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_mctx_765_);
lean_dec(v___x_764_);
v_lctx_766_ = lean_ctor_get(v___y_757_, 2);
v_options_767_ = lean_ctor_get(v___y_759_, 2);
lean_inc_ref(v_options_767_);
lean_inc_ref(v_lctx_766_);
v___x_768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_768_, 0, v_env_763_);
lean_ctor_set(v___x_768_, 1, v_mctx_765_);
lean_ctor_set(v___x_768_, 2, v_lctx_766_);
lean_ctor_set(v___x_768_, 3, v_options_767_);
v___x_769_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v_msgData_756_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_ref_784_; lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_ref_784_ = lean_ctor_get(v___y_781_, 5);
v___x_785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_ref_784_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_ref_784_);
lean_ctor_set(v___x_790_, 1, v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_829_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_829_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_noNatDivInst_x3f_822_; 
v_noNatDivInst_x3f_822_ = lean_ctor_get(v_a_818_, 11);
lean_inc(v_noNatDivInst_x3f_822_);
lean_dec(v_a_818_);
if (lean_obj_tag(v_noNatDivInst_x3f_822_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_825_; 
v_val_823_ = lean_ctor_get(v_noNatDivInst_x3f_822_, 0);
lean_inc(v_val_823_);
lean_dec_ref(v_noNatDivInst_x3f_822_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_val_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_val_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v_noNatDivInst_x3f_822_);
lean_del_object(v___x_820_);
v___x_827_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_828_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_827_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
return v___x_828_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_817_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_817_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec(v_a_839_);
lean_dec(v_a_838_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_851_, lean_object* v_msg_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_852_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_866_, lean_object* v_msg_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_866_, v_msg_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
return v_res_880_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_908_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_908_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_leInst_x3f_901_; 
v_leInst_x3f_901_ = lean_ctor_get(v_a_897_, 5);
lean_inc(v_leInst_x3f_901_);
lean_dec(v_a_897_);
if (lean_obj_tag(v_leInst_x3f_901_) == 1)
{
lean_object* v_val_902_; lean_object* v___x_904_; 
v_val_902_ = lean_ctor_get(v_leInst_x3f_901_, 0);
lean_inc(v_val_902_);
lean_dec_ref(v_leInst_x3f_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v_val_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_val_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec(v_leInst_x3f_901_);
lean_del_object(v___x_899_);
v___x_906_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_907_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_906_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_907_;
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_896_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_896_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec(v_a_918_);
lean_dec(v_a_917_);
return v_res_929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_957_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_ltInst_x3f_950_; 
v_ltInst_x3f_950_ = lean_ctor_get(v_a_946_, 6);
lean_inc(v_ltInst_x3f_950_);
lean_dec(v_a_946_);
if (lean_obj_tag(v_ltInst_x3f_950_) == 1)
{
lean_object* v_val_951_; lean_object* v___x_953_; 
v_val_951_ = lean_ctor_get(v_ltInst_x3f_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref(v_ltInst_x3f_950_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_val_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_val_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_ltInst_x3f_950_);
lean_del_object(v___x_948_);
v___x_955_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_956_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_955_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_956_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_945_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_945_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec(v_a_967_);
lean_dec(v_a_966_);
return v_res_978_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1006_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_lawfulOrderLTInst_x3f_999_; 
v_lawfulOrderLTInst_x3f_999_ = lean_ctor_get(v_a_995_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_999_);
lean_dec(v_a_995_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_999_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1002_; 
v_val_1000_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_999_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_val_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_lawfulOrderLTInst_x3f_999_);
lean_del_object(v___x_997_);
v___x_1004_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1005_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1004_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_994_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_994_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec(v_a_1015_);
return v_res_1027_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1055_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1055_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_isPreorderInst_x3f_1048_; 
v_isPreorderInst_x3f_1048_ = lean_ctor_get(v_a_1044_, 8);
lean_inc(v_isPreorderInst_x3f_1048_);
lean_dec(v_a_1044_);
if (lean_obj_tag(v_isPreorderInst_x3f_1048_) == 1)
{
lean_object* v_val_1049_; lean_object* v___x_1051_; 
v_val_1049_ = lean_ctor_get(v_isPreorderInst_x3f_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref(v_isPreorderInst_x3f_1048_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_val_1049_);
v___x_1051_ = v___x_1046_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_val_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_isPreorderInst_x3f_1048_);
lean_del_object(v___x_1046_);
v___x_1053_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1054_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1053_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1054_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1043_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1043_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1104_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_orderedAddInst_x3f_1097_; 
v_orderedAddInst_x3f_1097_ = lean_ctor_get(v_a_1093_, 9);
lean_inc(v_orderedAddInst_x3f_1097_);
lean_dec(v_a_1093_);
if (lean_obj_tag(v_orderedAddInst_x3f_1097_) == 1)
{
lean_object* v_val_1098_; lean_object* v___x_1100_; 
v_val_1098_ = lean_ctor_get(v_orderedAddInst_x3f_1097_, 0);
lean_inc(v_val_1098_);
lean_dec_ref(v_orderedAddInst_x3f_1097_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_val_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_val_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec(v_orderedAddInst_x3f_1097_);
lean_del_object(v___x_1095_);
v___x_1102_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1103_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1102_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1092_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1092_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1154_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1154_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_orderedAddInst_x3f_1143_; 
v_orderedAddInst_x3f_1143_ = lean_ctor_get(v_a_1139_, 9);
lean_inc(v_orderedAddInst_x3f_1143_);
lean_dec(v_a_1139_);
if (lean_obj_tag(v_orderedAddInst_x3f_1143_) == 0)
{
uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = 0;
v___x_1145_ = lean_box(v___x_1144_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1147_ = v___x_1141_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec_ref(v_orderedAddInst_x3f_1143_);
v___x_1149_ = 1;
v___x_1150_ = lean_box(v___x_1149_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1150_);
v___x_1152_ = v___x_1141_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1138_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1138_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_____do__lift_1179_){
_start:
{
lean_object* v_ltFn_x3f_1180_; 
v_ltFn_x3f_1180_ = lean_ctor_get(v_____do__lift_1179_, 21);
lean_inc(v_ltFn_x3f_1180_);
lean_dec_ref(v_____do__lift_1179_);
if (lean_obj_tag(v_ltFn_x3f_1180_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v_inst_1178_);
lean_dec_ref(v_inst_1177_);
v_val_1181_ = lean_ctor_get(v_ltFn_x3f_1180_, 0);
lean_inc(v_val_1181_);
lean_dec_ref(v_ltFn_x3f_1180_);
v___x_1182_ = lean_apply_2(v_toPure_1176_, lean_box(0), v_val_1181_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_ltFn_x3f_1180_);
lean_dec(v_toPure_1176_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1184_ = l_Lean_throwError___redArg(v_inst_1177_, v_inst_1178_, v___x_1183_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_){
_start:
{
lean_object* v_toApplicative_1188_; lean_object* v_toBind_1189_; lean_object* v_toPure_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v_toApplicative_1188_ = lean_ctor_get(v_inst_1185_, 0);
v_toBind_1189_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc(v_toBind_1189_);
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1188_, 1);
lean_inc(v_toPure_1190_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1191_, 0, v_toPure_1190_);
lean_closure_set(v___f_1191_, 1, v_inst_1185_);
lean_closure_set(v___f_1191_, 2, v_inst_1186_);
v___x_1192_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v_inst_1187_, v___f_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1194_, v_inst_1195_, v_inst_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1200_ = l_Lean_stringToMessageData(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_____do__lift_1204_){
_start:
{
lean_object* v_leFn_x3f_1205_; 
v_leFn_x3f_1205_ = lean_ctor_get(v_____do__lift_1204_, 20);
lean_inc(v_leFn_x3f_1205_);
lean_dec_ref(v_____do__lift_1204_);
if (lean_obj_tag(v_leFn_x3f_1205_) == 1)
{
lean_object* v_val_1206_; lean_object* v___x_1207_; 
lean_dec_ref(v_inst_1203_);
lean_dec_ref(v_inst_1202_);
v_val_1206_ = lean_ctor_get(v_leFn_x3f_1205_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v_leFn_x3f_1205_);
v___x_1207_ = lean_apply_2(v_toPure_1201_, lean_box(0), v_val_1206_);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_leFn_x3f_1205_);
lean_dec(v_toPure_1201_);
v___x_1208_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1209_ = l_Lean_throwError___redArg(v_inst_1202_, v_inst_1203_, v___x_1208_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_){
_start:
{
lean_object* v_toApplicative_1213_; lean_object* v_toBind_1214_; lean_object* v_toPure_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; 
v_toApplicative_1213_ = lean_ctor_get(v_inst_1210_, 0);
v_toBind_1214_ = lean_ctor_get(v_inst_1210_, 1);
lean_inc(v_toBind_1214_);
v_toPure_1215_ = lean_ctor_get(v_toApplicative_1213_, 1);
lean_inc(v_toPure_1215_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1216_, 0, v_toPure_1215_);
lean_closure_set(v___f_1216_, 1, v_inst_1210_);
lean_closure_set(v___f_1216_, 2, v_inst_1211_);
v___x_1217_ = lean_apply_4(v_toBind_1214_, lean_box(0), lean_box(0), v_inst_1212_, v___f_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1219_, v_inst_1220_, v_inst_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1225_ = l_Lean_stringToMessageData(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1250_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1250_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_isLinearInst_x3f_1243_; 
v_isLinearInst_x3f_1243_ = lean_ctor_get(v_a_1239_, 10);
lean_inc(v_isLinearInst_x3f_1243_);
lean_dec(v_a_1239_);
if (lean_obj_tag(v_isLinearInst_x3f_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1246_; 
v_val_1244_ = lean_ctor_get(v_isLinearInst_x3f_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v_isLinearInst_x3f_1243_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v_val_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_val_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec(v_isLinearInst_x3f_1243_);
lean_del_object(v___x_1241_);
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1249_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1248_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1238_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1238_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec(v_a_1259_);
return v_res_1271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1274_ = l_Lean_stringToMessageData(v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1299_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1299_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1299_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_ringInst_x3f_1292_; 
v_ringInst_x3f_1292_ = lean_ctor_get(v_a_1288_, 12);
lean_inc(v_ringInst_x3f_1292_);
lean_dec(v_a_1288_);
if (lean_obj_tag(v_ringInst_x3f_1292_) == 1)
{
lean_object* v_val_1293_; lean_object* v___x_1295_; 
v_val_1293_ = lean_ctor_get(v_ringInst_x3f_1292_, 0);
lean_inc(v_val_1293_);
lean_dec_ref(v_ringInst_x3f_1292_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_val_1293_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_ringInst_x3f_1292_);
lean_del_object(v___x_1290_);
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1298_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1297_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1287_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1287_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec(v_a_1308_);
return v_res_1320_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1348_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_commRingInst_x3f_1341_; 
v_commRingInst_x3f_1341_ = lean_ctor_get(v_a_1337_, 13);
lean_inc(v_commRingInst_x3f_1341_);
lean_dec(v_a_1337_);
if (lean_obj_tag(v_commRingInst_x3f_1341_) == 1)
{
lean_object* v_val_1342_; lean_object* v___x_1344_; 
v_val_1342_ = lean_ctor_get(v_commRingInst_x3f_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref(v_commRingInst_x3f_1341_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_val_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_val_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v_commRingInst_x3f_1341_);
lean_del_object(v___x_1339_);
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1347_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1346_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1347_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1336_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1336_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
return v_res_1369_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1397_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_orderedRingInst_x3f_1390_; 
v_orderedRingInst_x3f_1390_ = lean_ctor_get(v_a_1386_, 14);
lean_inc(v_orderedRingInst_x3f_1390_);
lean_dec(v_a_1386_);
if (lean_obj_tag(v_orderedRingInst_x3f_1390_) == 1)
{
lean_object* v_val_1391_; lean_object* v___x_1393_; 
v_val_1391_ = lean_ctor_get(v_orderedRingInst_x3f_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v_orderedRingInst_x3f_1390_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_val_1391_);
v___x_1393_ = v___x_1388_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_val_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_orderedRingInst_x3f_1390_);
lean_del_object(v___x_1388_);
v___x_1395_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1396_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1395_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1385_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1385_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
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
lean_dec(v_a_1406_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Rat_ofInt(v_a_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1421_, lean_object* v_v_1422_, lean_object* v_a_1423_){
_start:
{
if (lean_obj_tag(v_a_1423_) == 0)
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_v_1422_);
return v___x_1424_;
}
else
{
lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v_p_1427_; lean_object* v_size_1428_; uint8_t v___x_1429_; 
v_k_1425_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_k_1425_);
v_v_1426_ = lean_ctor_get(v_a_1423_, 1);
lean_inc(v_v_1426_);
v_p_1427_ = lean_ctor_get(v_a_1423_, 2);
lean_inc(v_p_1427_);
lean_dec_ref(v_a_1423_);
v_size_1428_ = lean_ctor_get(v_a_1421_, 2);
v___x_1429_ = lean_nat_dec_lt(v_v_1426_, v_size_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_p_1427_);
lean_dec(v_v_1426_);
lean_dec(v_k_1425_);
lean_dec_ref(v_v_1422_);
v___x_1430_ = lean_box(0);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1431_ = l_Rat_ofInt(v_k_1425_);
v___x_1432_ = l_instInhabitedRat;
v___x_1433_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1432_, v_a_1421_, v_v_1426_);
lean_dec(v_v_1426_);
v___x_1434_ = l_Rat_mul(v___x_1431_, v___x_1433_);
lean_dec_ref(v___x_1431_);
v___x_1435_ = l_Rat_add(v_v_1422_, v___x_1434_);
v_v_1422_ = v___x_1435_;
v_a_1423_ = v_p_1427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1437_, lean_object* v_v_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1437_, v_v_1438_, v_a_1439_);
lean_dec_ref(v_a_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_nat_to_int(v_a_1441_);
v___x_1443_ = l_Rat_ofInt(v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1470_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1470_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1470_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_assignment_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v_assignment_1464_ = lean_ctor_get(v_a_1460_, 35);
lean_inc_ref(v_assignment_1464_);
lean_dec(v_a_1460_);
v___x_1465_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1466_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1464_, v___x_1465_, v_p_1446_);
lean_dec_ref(v_assignment_1464_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1466_);
v___x_1468_ = v___x_1462_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_p_1446_);
v_a_1471_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1459_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1459_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec(v_a_1480_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_nat_to_int(v_a_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_p_1508_; uint8_t v_strict_1509_; lean_object* v___x_1510_; 
v_p_1508_ = lean_ctor_get(v_c_1495_, 0);
lean_inc(v_p_1508_);
v_strict_1509_ = lean_ctor_get_uint8(v_c_1495_, sizeof(void*)*2);
lean_dec_ref(v_c_1495_);
v___x_1510_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1508_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1536_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1536_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1536_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
if (lean_obj_tag(v_a_1511_) == 1)
{
if (v_strict_1509_ == 0)
{
lean_object* v_val_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v_val_1515_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_val_1515_);
lean_dec_ref(v_a_1511_);
v___x_1516_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1517_ = l_Rat_instDecidableLe(v_val_1515_, v___x_1516_);
v___x_1518_ = l_Bool_toLBool(v___x_1517_);
v___x_1519_ = lean_box(v___x_1518_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1519_);
v___x_1521_ = v___x_1513_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
else
{
lean_object* v_val_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v_val_1523_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v_a_1511_);
v___x_1524_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1525_ = l_Rat_blt(v_val_1523_, v___x_1524_);
v___x_1526_ = l_Bool_toLBool(v___x_1525_);
v___x_1527_ = lean_box(v___x_1526_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1527_);
v___x_1529_ = v___x_1513_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_dec(v_a_1511_);
v___x_1531_ = 2;
v___x_1532_ = lean_box(v___x_1531_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1532_);
v___x_1534_ = v___x_1513_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1510_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1510_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec(v_a_1546_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_p_1572_; lean_object* v___x_1573_; 
v_p_1572_ = lean_ctor_get(v_c_1559_, 0);
lean_inc(v_p_1572_);
lean_dec_ref(v_c_1559_);
v___x_1573_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1572_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1593_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1593_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
uint8_t v___y_1579_; 
if (lean_obj_tag(v_a_1574_) == 1)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_val_1585_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_val_1585_);
lean_dec_ref(v_a_1574_);
v___x_1586_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1587_ = l_instDecidableEqRat_decEq(v_val_1585_, v___x_1586_);
lean_dec(v_val_1585_);
if (v___x_1587_ == 0)
{
uint8_t v___x_1588_; 
v___x_1588_ = 1;
v___y_1579_ = v___x_1588_;
goto v___jp_1578_;
}
else
{
uint8_t v___x_1589_; 
v___x_1589_ = 0;
v___y_1579_ = v___x_1589_;
goto v___jp_1578_;
}
}
else
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_del_object(v___x_1576_);
lean_dec(v_a_1574_);
v___x_1590_ = 2;
v___x_1591_ = lean_box(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
v___jp_1578_:
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = l_Bool_toLBool(v___y_1579_);
v___x_1581_ = lean_box(v___x_1580_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1581_);
v___x_1583_ = v___x_1576_;
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
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1573_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1573_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1616_, lean_object* v_x_1617_, lean_object* v_s_1618_){
_start:
{
lean_object* v_structs_1619_; lean_object* v_typeIdOf_1620_; lean_object* v_exprToStructId_1621_; lean_object* v_exprToStructIdEntries_1622_; lean_object* v_forbiddenNatModules_1623_; lean_object* v_natStructs_1624_; lean_object* v_natTypeIdOf_1625_; lean_object* v_exprToNatStructId_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_structs_1619_ = lean_ctor_get(v_s_1618_, 0);
v_typeIdOf_1620_ = lean_ctor_get(v_s_1618_, 1);
v_exprToStructId_1621_ = lean_ctor_get(v_s_1618_, 2);
v_exprToStructIdEntries_1622_ = lean_ctor_get(v_s_1618_, 3);
v_forbiddenNatModules_1623_ = lean_ctor_get(v_s_1618_, 4);
v_natStructs_1624_ = lean_ctor_get(v_s_1618_, 5);
v_natTypeIdOf_1625_ = lean_ctor_get(v_s_1618_, 6);
v_exprToNatStructId_1626_ = lean_ctor_get(v_s_1618_, 7);
v___x_1627_ = lean_array_get_size(v_structs_1619_);
v___x_1628_ = lean_nat_dec_lt(v_a_1616_, v___x_1627_);
if (v___x_1628_ == 0)
{
return v_s_1618_;
}
else
{
lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1690_; 
lean_inc_ref(v_exprToNatStructId_1626_);
lean_inc_ref(v_natTypeIdOf_1625_);
lean_inc_ref(v_natStructs_1624_);
lean_inc_ref(v_forbiddenNatModules_1623_);
lean_inc_ref(v_exprToStructIdEntries_1622_);
lean_inc_ref(v_exprToStructId_1621_);
lean_inc_ref(v_typeIdOf_1620_);
lean_inc_ref(v_structs_1619_);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_s_1618_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; lean_object* v_unused_1695_; lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; 
v_unused_1691_ = lean_ctor_get(v_s_1618_, 7);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_s_1618_, 6);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_s_1618_, 5);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_s_1618_, 4);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_s_1618_, 3);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_s_1618_, 2);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_s_1618_, 1);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_s_1618_, 0);
lean_dec(v_unused_1698_);
v___x_1630_ = v_s_1618_;
v_isShared_1631_ = v_isSharedCheck_1690_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_s_1618_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1690_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_v_1632_; lean_object* v_id_1633_; lean_object* v_ringId_x3f_1634_; lean_object* v_type_1635_; lean_object* v_u_1636_; lean_object* v_intModuleInst_1637_; lean_object* v_leInst_x3f_1638_; lean_object* v_ltInst_x3f_1639_; lean_object* v_lawfulOrderLTInst_x3f_1640_; lean_object* v_isPreorderInst_x3f_1641_; lean_object* v_orderedAddInst_x3f_1642_; lean_object* v_isLinearInst_x3f_1643_; lean_object* v_noNatDivInst_x3f_1644_; lean_object* v_ringInst_x3f_1645_; lean_object* v_commRingInst_x3f_1646_; lean_object* v_orderedRingInst_x3f_1647_; lean_object* v_fieldInst_x3f_1648_; lean_object* v_charInst_x3f_1649_; lean_object* v_zero_1650_; lean_object* v_ofNatZero_1651_; lean_object* v_one_x3f_1652_; lean_object* v_leFn_x3f_1653_; lean_object* v_ltFn_x3f_1654_; lean_object* v_addFn_1655_; lean_object* v_zsmulFn_1656_; lean_object* v_nsmulFn_1657_; lean_object* v_zsmulFn_x3f_1658_; lean_object* v_nsmulFn_x3f_1659_; lean_object* v_homomulFn_x3f_1660_; lean_object* v_subFn_1661_; lean_object* v_negFn_1662_; lean_object* v_vars_1663_; lean_object* v_varMap_1664_; lean_object* v_lowers_1665_; lean_object* v_uppers_1666_; lean_object* v_diseqs_1667_; lean_object* v_assignment_1668_; uint8_t v_caseSplits_1669_; lean_object* v_conflict_x3f_1670_; lean_object* v_diseqSplits_1671_; lean_object* v_elimEqs_1672_; lean_object* v_elimStack_1673_; lean_object* v_occurs_1674_; lean_object* v_ignored_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1689_; 
v_v_1632_ = lean_array_fget(v_structs_1619_, v_a_1616_);
v_id_1633_ = lean_ctor_get(v_v_1632_, 0);
v_ringId_x3f_1634_ = lean_ctor_get(v_v_1632_, 1);
v_type_1635_ = lean_ctor_get(v_v_1632_, 2);
v_u_1636_ = lean_ctor_get(v_v_1632_, 3);
v_intModuleInst_1637_ = lean_ctor_get(v_v_1632_, 4);
v_leInst_x3f_1638_ = lean_ctor_get(v_v_1632_, 5);
v_ltInst_x3f_1639_ = lean_ctor_get(v_v_1632_, 6);
v_lawfulOrderLTInst_x3f_1640_ = lean_ctor_get(v_v_1632_, 7);
v_isPreorderInst_x3f_1641_ = lean_ctor_get(v_v_1632_, 8);
v_orderedAddInst_x3f_1642_ = lean_ctor_get(v_v_1632_, 9);
v_isLinearInst_x3f_1643_ = lean_ctor_get(v_v_1632_, 10);
v_noNatDivInst_x3f_1644_ = lean_ctor_get(v_v_1632_, 11);
v_ringInst_x3f_1645_ = lean_ctor_get(v_v_1632_, 12);
v_commRingInst_x3f_1646_ = lean_ctor_get(v_v_1632_, 13);
v_orderedRingInst_x3f_1647_ = lean_ctor_get(v_v_1632_, 14);
v_fieldInst_x3f_1648_ = lean_ctor_get(v_v_1632_, 15);
v_charInst_x3f_1649_ = lean_ctor_get(v_v_1632_, 16);
v_zero_1650_ = lean_ctor_get(v_v_1632_, 17);
v_ofNatZero_1651_ = lean_ctor_get(v_v_1632_, 18);
v_one_x3f_1652_ = lean_ctor_get(v_v_1632_, 19);
v_leFn_x3f_1653_ = lean_ctor_get(v_v_1632_, 20);
v_ltFn_x3f_1654_ = lean_ctor_get(v_v_1632_, 21);
v_addFn_1655_ = lean_ctor_get(v_v_1632_, 22);
v_zsmulFn_1656_ = lean_ctor_get(v_v_1632_, 23);
v_nsmulFn_1657_ = lean_ctor_get(v_v_1632_, 24);
v_zsmulFn_x3f_1658_ = lean_ctor_get(v_v_1632_, 25);
v_nsmulFn_x3f_1659_ = lean_ctor_get(v_v_1632_, 26);
v_homomulFn_x3f_1660_ = lean_ctor_get(v_v_1632_, 27);
v_subFn_1661_ = lean_ctor_get(v_v_1632_, 28);
v_negFn_1662_ = lean_ctor_get(v_v_1632_, 29);
v_vars_1663_ = lean_ctor_get(v_v_1632_, 30);
v_varMap_1664_ = lean_ctor_get(v_v_1632_, 31);
v_lowers_1665_ = lean_ctor_get(v_v_1632_, 32);
v_uppers_1666_ = lean_ctor_get(v_v_1632_, 33);
v_diseqs_1667_ = lean_ctor_get(v_v_1632_, 34);
v_assignment_1668_ = lean_ctor_get(v_v_1632_, 35);
v_caseSplits_1669_ = lean_ctor_get_uint8(v_v_1632_, sizeof(void*)*42);
v_conflict_x3f_1670_ = lean_ctor_get(v_v_1632_, 36);
v_diseqSplits_1671_ = lean_ctor_get(v_v_1632_, 37);
v_elimEqs_1672_ = lean_ctor_get(v_v_1632_, 38);
v_elimStack_1673_ = lean_ctor_get(v_v_1632_, 39);
v_occurs_1674_ = lean_ctor_get(v_v_1632_, 40);
v_ignored_1675_ = lean_ctor_get(v_v_1632_, 41);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_v_1632_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1677_ = v_v_1632_;
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_ignored_1675_);
lean_inc(v_occurs_1674_);
lean_inc(v_elimStack_1673_);
lean_inc(v_elimEqs_1672_);
lean_inc(v_diseqSplits_1671_);
lean_inc(v_conflict_x3f_1670_);
lean_inc(v_assignment_1668_);
lean_inc(v_diseqs_1667_);
lean_inc(v_uppers_1666_);
lean_inc(v_lowers_1665_);
lean_inc(v_varMap_1664_);
lean_inc(v_vars_1663_);
lean_inc(v_negFn_1662_);
lean_inc(v_subFn_1661_);
lean_inc(v_homomulFn_x3f_1660_);
lean_inc(v_nsmulFn_x3f_1659_);
lean_inc(v_zsmulFn_x3f_1658_);
lean_inc(v_nsmulFn_1657_);
lean_inc(v_zsmulFn_1656_);
lean_inc(v_addFn_1655_);
lean_inc(v_ltFn_x3f_1654_);
lean_inc(v_leFn_x3f_1653_);
lean_inc(v_one_x3f_1652_);
lean_inc(v_ofNatZero_1651_);
lean_inc(v_zero_1650_);
lean_inc(v_charInst_x3f_1649_);
lean_inc(v_fieldInst_x3f_1648_);
lean_inc(v_orderedRingInst_x3f_1647_);
lean_inc(v_commRingInst_x3f_1646_);
lean_inc(v_ringInst_x3f_1645_);
lean_inc(v_noNatDivInst_x3f_1644_);
lean_inc(v_isLinearInst_x3f_1643_);
lean_inc(v_orderedAddInst_x3f_1642_);
lean_inc(v_isPreorderInst_x3f_1641_);
lean_inc(v_lawfulOrderLTInst_x3f_1640_);
lean_inc(v_ltInst_x3f_1639_);
lean_inc(v_leInst_x3f_1638_);
lean_inc(v_intModuleInst_1637_);
lean_inc(v_u_1636_);
lean_inc(v_type_1635_);
lean_inc(v_ringId_x3f_1634_);
lean_inc(v_id_1633_);
lean_dec(v_v_1632_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v_xs_x27_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1679_ = lean_box(0);
v_xs_x27_1680_ = lean_array_fset(v_structs_1619_, v_a_1616_, v___x_1679_);
v___x_1681_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1668_, v_x_1617_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 35, v___x_1681_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_id_1633_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_ringId_x3f_1634_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_type_1635_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_u_1636_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_intModuleInst_1637_);
lean_ctor_set(v_reuseFailAlloc_1688_, 5, v_leInst_x3f_1638_);
lean_ctor_set(v_reuseFailAlloc_1688_, 6, v_ltInst_x3f_1639_);
lean_ctor_set(v_reuseFailAlloc_1688_, 7, v_lawfulOrderLTInst_x3f_1640_);
lean_ctor_set(v_reuseFailAlloc_1688_, 8, v_isPreorderInst_x3f_1641_);
lean_ctor_set(v_reuseFailAlloc_1688_, 9, v_orderedAddInst_x3f_1642_);
lean_ctor_set(v_reuseFailAlloc_1688_, 10, v_isLinearInst_x3f_1643_);
lean_ctor_set(v_reuseFailAlloc_1688_, 11, v_noNatDivInst_x3f_1644_);
lean_ctor_set(v_reuseFailAlloc_1688_, 12, v_ringInst_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1688_, 13, v_commRingInst_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1688_, 14, v_orderedRingInst_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1688_, 15, v_fieldInst_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1688_, 16, v_charInst_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1688_, 17, v_zero_1650_);
lean_ctor_set(v_reuseFailAlloc_1688_, 18, v_ofNatZero_1651_);
lean_ctor_set(v_reuseFailAlloc_1688_, 19, v_one_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1688_, 20, v_leFn_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1688_, 21, v_ltFn_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1688_, 22, v_addFn_1655_);
lean_ctor_set(v_reuseFailAlloc_1688_, 23, v_zsmulFn_1656_);
lean_ctor_set(v_reuseFailAlloc_1688_, 24, v_nsmulFn_1657_);
lean_ctor_set(v_reuseFailAlloc_1688_, 25, v_zsmulFn_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1688_, 26, v_nsmulFn_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1688_, 27, v_homomulFn_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1688_, 28, v_subFn_1661_);
lean_ctor_set(v_reuseFailAlloc_1688_, 29, v_negFn_1662_);
lean_ctor_set(v_reuseFailAlloc_1688_, 30, v_vars_1663_);
lean_ctor_set(v_reuseFailAlloc_1688_, 31, v_varMap_1664_);
lean_ctor_set(v_reuseFailAlloc_1688_, 32, v_lowers_1665_);
lean_ctor_set(v_reuseFailAlloc_1688_, 33, v_uppers_1666_);
lean_ctor_set(v_reuseFailAlloc_1688_, 34, v_diseqs_1667_);
lean_ctor_set(v_reuseFailAlloc_1688_, 35, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1688_, 36, v_conflict_x3f_1670_);
lean_ctor_set(v_reuseFailAlloc_1688_, 37, v_diseqSplits_1671_);
lean_ctor_set(v_reuseFailAlloc_1688_, 38, v_elimEqs_1672_);
lean_ctor_set(v_reuseFailAlloc_1688_, 39, v_elimStack_1673_);
lean_ctor_set(v_reuseFailAlloc_1688_, 40, v_occurs_1674_);
lean_ctor_set(v_reuseFailAlloc_1688_, 41, v_ignored_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1688_, sizeof(void*)*42, v_caseSplits_1669_);
v___x_1683_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_array_fset(v_xs_x27_1680_, v_a_1616_, v___x_1683_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1684_);
v___x_1686_ = v___x_1630_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_typeIdOf_1620_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_exprToStructId_1621_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_exprToStructIdEntries_1622_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_forbiddenNatModules_1623_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v_natStructs_1624_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_natTypeIdOf_1625_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_exprToNatStructId_1626_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1699_, lean_object* v_x_1700_, lean_object* v_s_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1699_, v_x_1700_, v_s_1701_);
lean_dec(v_x_1700_);
lean_dec(v_a_1699_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_inc(v_a_1704_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1707_, 0, v_a_1704_);
lean_closure_set(v___f_1707_, 1, v_x_1703_);
v___x_1708_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1709_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1708_, v___f_1707_, v_a_1705_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec(v_a_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1715_, v_a_1716_, v_a_1717_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec(v_a_1730_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1773_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1773_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1773_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_vars_1761_; lean_object* v_size_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_vars_1761_ = lean_ctor_get(v_a_1757_, 30);
lean_inc_ref(v_vars_1761_);
lean_dec(v_a_1757_);
v_size_1762_ = lean_ctor_get(v_vars_1761_, 2);
v___x_1763_ = l_Lean_instInhabitedExpr;
v___x_1764_ = lean_nat_dec_lt(v_x_1743_, v_size_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_dec_ref(v_vars_1761_);
v___x_1765_ = l_outOfBounds___redArg(v___x_1763_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1765_);
v___x_1767_ = v___x_1759_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1763_, v_vars_1761_, v_x_1743_);
lean_dec_ref(v_vars_1761_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1769_);
v___x_1771_ = v___x_1759_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_a_1774_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1756_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1756_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec(v_x_1782_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1797_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; uint8_t v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
v___x_1810_ = lean_unbox(v_a_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v___x_1808_);
v___x_1811_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1825_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_conflict_x3f_1816_; 
v_conflict_x3f_1816_ = lean_ctor_get(v_a_1812_, 36);
lean_inc(v_conflict_x3f_1816_);
lean_dec(v_a_1812_);
if (lean_obj_tag(v_conflict_x3f_1816_) == 0)
{
lean_object* v___x_1818_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_a_1809_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1809_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec_ref(v_conflict_x3f_1816_);
lean_dec(v_a_1809_);
v___x_1820_ = 1;
v___x_1821_ = lean_box(v___x_1820_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1821_);
v___x_1823_ = v___x_1814_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_a_1809_);
v_a_1826_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1811_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1811_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_dec(v_a_1809_);
return v___x_1808_;
}
}
else
{
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec(v_a_1834_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1883_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1883_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1883_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___y_1866_; lean_object* v_elimEqs_1877_; lean_object* v_size_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_elimEqs_1877_ = lean_ctor_get(v_a_1861_, 38);
lean_inc_ref(v_elimEqs_1877_);
lean_dec(v_a_1861_);
v_size_1878_ = lean_ctor_get(v_elimEqs_1877_, 2);
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_nat_dec_lt(v_x_1847_, v_size_1878_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
lean_dec_ref(v_elimEqs_1877_);
v___x_1881_ = l_outOfBounds___redArg(v___x_1879_);
v___y_1866_ = v___x_1881_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1879_, v_elimEqs_1877_, v_x_1847_);
lean_dec_ref(v_elimEqs_1877_);
v___y_1866_ = v___x_1882_;
goto v___jp_1865_;
}
v___jp_1865_:
{
if (lean_obj_tag(v___y_1866_) == 0)
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = 0;
v___x_1868_ = lean_box(v___x_1867_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1868_);
v___x_1870_ = v___x_1863_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
else
{
uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec_ref(v___y_1866_);
v___x_1872_ = 1;
v___x_1873_ = lean_box(v___x_1872_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1873_);
v___x_1875_ = v___x_1863_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1860_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1860_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_x_1892_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1936_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1936_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1936_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_occurs_1924_; lean_object* v_size_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_occurs_1924_ = lean_ctor_get(v_a_1920_, 40);
lean_inc_ref(v_occurs_1924_);
lean_dec(v_a_1920_);
v_size_1925_ = lean_ctor_get(v_occurs_1924_, 2);
v___x_1926_ = lean_box(1);
v___x_1927_ = lean_nat_dec_lt(v_x_1906_, v_size_1925_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_dec_ref(v_occurs_1924_);
v___x_1928_ = l_outOfBounds___redArg(v___x_1926_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1928_);
v___x_1930_ = v___x_1922_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1926_, v_occurs_1924_, v_x_1906_);
lean_dec_ref(v_occurs_1924_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1932_);
v___x_1934_ = v___x_1922_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
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
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1919_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1919_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec(v_x_1945_);
return v_res_1958_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1959_, lean_object* v_t_1960_){
_start:
{
if (lean_obj_tag(v_t_1960_) == 0)
{
lean_object* v_k_1961_; lean_object* v_l_1962_; lean_object* v_r_1963_; uint8_t v___x_1964_; 
v_k_1961_ = lean_ctor_get(v_t_1960_, 1);
v_l_1962_ = lean_ctor_get(v_t_1960_, 3);
v_r_1963_ = lean_ctor_get(v_t_1960_, 4);
v___x_1964_ = lean_nat_dec_lt(v_k_1959_, v_k_1961_);
if (v___x_1964_ == 0)
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_nat_dec_eq(v_k_1959_, v_k_1961_);
if (v___x_1965_ == 0)
{
v_t_1960_ = v_r_1963_;
goto _start;
}
else
{
return v___x_1965_;
}
}
else
{
v_t_1960_ = v_l_1962_;
goto _start;
}
}
else
{
uint8_t v___x_1968_; 
v___x_1968_ = 0;
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1969_, lean_object* v_t_1970_){
_start:
{
uint8_t v_res_1971_; lean_object* v_r_1972_; 
v_res_1971_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1969_, v_t_1970_);
lean_dec(v_t_1970_);
lean_dec(v_k_1969_);
v_r_1972_ = lean_box(v_res_1971_);
return v_r_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1973_, lean_object* v_v_1974_, lean_object* v_t_1975_){
_start:
{
if (lean_obj_tag(v_t_1975_) == 0)
{
lean_object* v_size_1976_; lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v_l_1979_; lean_object* v_r_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2261_; 
v_size_1976_ = lean_ctor_get(v_t_1975_, 0);
v_k_1977_ = lean_ctor_get(v_t_1975_, 1);
v_v_1978_ = lean_ctor_get(v_t_1975_, 2);
v_l_1979_ = lean_ctor_get(v_t_1975_, 3);
v_r_1980_ = lean_ctor_get(v_t_1975_, 4);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_t_1975_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_1982_ = v_t_1975_;
v_isShared_1983_ = v_isSharedCheck_2261_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_r_1980_);
lean_inc(v_l_1979_);
lean_inc(v_v_1978_);
lean_inc(v_k_1977_);
lean_inc(v_size_1976_);
lean_dec(v_t_1975_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2261_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_nat_dec_lt(v_k_1973_, v_k_1977_);
if (v___x_1984_ == 0)
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_nat_dec_eq(v_k_1973_, v_k_1977_);
if (v___x_1985_ == 0)
{
lean_object* v_impl_1986_; lean_object* v___x_1987_; 
lean_dec(v_size_1976_);
v_impl_1986_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1973_, v_v_1974_, v_r_1980_);
v___x_1987_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1979_) == 0)
{
lean_object* v_size_1988_; lean_object* v_size_1989_; lean_object* v_k_1990_; lean_object* v_v_1991_; lean_object* v_l_1992_; lean_object* v_r_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_size_1988_ = lean_ctor_get(v_l_1979_, 0);
v_size_1989_ = lean_ctor_get(v_impl_1986_, 0);
lean_inc(v_size_1989_);
v_k_1990_ = lean_ctor_get(v_impl_1986_, 1);
lean_inc(v_k_1990_);
v_v_1991_ = lean_ctor_get(v_impl_1986_, 2);
lean_inc(v_v_1991_);
v_l_1992_ = lean_ctor_get(v_impl_1986_, 3);
lean_inc(v_l_1992_);
v_r_1993_ = lean_ctor_get(v_impl_1986_, 4);
lean_inc(v_r_1993_);
v___x_1994_ = lean_unsigned_to_nat(3u);
v___x_1995_ = lean_nat_mul(v___x_1994_, v_size_1988_);
v___x_1996_ = lean_nat_dec_lt(v___x_1995_, v_size_1989_);
lean_dec(v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_r_1993_);
lean_dec(v_l_1992_);
lean_dec(v_v_1991_);
lean_dec(v_k_1990_);
v___x_1997_ = lean_nat_add(v___x_1987_, v_size_1988_);
v___x_1998_ = lean_nat_add(v___x_1997_, v_size_1989_);
lean_dec(v_size_1989_);
lean_dec(v___x_1997_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_impl_1986_);
lean_ctor_set(v___x_1982_, 0, v___x_1998_);
v___x_2000_ = v___x_1982_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_impl_1986_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
else
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v_impl_1986_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; 
v_unused_2066_ = lean_ctor_get(v_impl_1986_, 4);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_impl_1986_, 3);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_impl_1986_, 2);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_impl_1986_, 1);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_impl_1986_, 0);
lean_dec(v_unused_2070_);
v___x_2003_ = v_impl_1986_;
v_isShared_2004_ = v_isSharedCheck_2065_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_impl_1986_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2065_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_size_2005_; lean_object* v_k_2006_; lean_object* v_v_2007_; lean_object* v_l_2008_; lean_object* v_r_2009_; lean_object* v_size_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_size_2005_ = lean_ctor_get(v_l_1992_, 0);
v_k_2006_ = lean_ctor_get(v_l_1992_, 1);
v_v_2007_ = lean_ctor_get(v_l_1992_, 2);
v_l_2008_ = lean_ctor_get(v_l_1992_, 3);
v_r_2009_ = lean_ctor_get(v_l_1992_, 4);
v_size_2010_ = lean_ctor_get(v_r_1993_, 0);
v___x_2011_ = lean_unsigned_to_nat(2u);
v___x_2012_ = lean_nat_mul(v___x_2011_, v_size_2010_);
v___x_2013_ = lean_nat_dec_lt(v_size_2005_, v___x_2012_);
lean_dec(v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2041_; 
lean_inc(v_r_2009_);
lean_inc(v_l_2008_);
lean_inc(v_v_2007_);
lean_inc(v_k_2006_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_l_1992_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2042_ = lean_ctor_get(v_l_1992_, 4);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_l_1992_, 3);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_l_1992_, 2);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_l_1992_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_l_1992_, 0);
lean_dec(v_unused_2046_);
v___x_2015_ = v_l_1992_;
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v_l_1992_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2031_; 
v___x_2017_ = lean_nat_add(v___x_1987_, v_size_1988_);
v___x_2018_ = lean_nat_add(v___x_2017_, v_size_1989_);
lean_dec(v_size_1989_);
if (lean_obj_tag(v_l_2008_) == 0)
{
lean_object* v_size_2039_; 
v_size_2039_ = lean_ctor_get(v_l_2008_, 0);
lean_inc(v_size_2039_);
v___y_2031_ = v_size_2039_;
goto v___jp_2030_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___y_2031_ = v___x_2040_;
goto v___jp_2030_;
}
v___jp_2019_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_nat_add(v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 4, v_r_1993_);
lean_ctor_set(v___x_2015_, 3, v_r_2009_);
lean_ctor_set(v___x_2015_, 2, v_v_1991_);
lean_ctor_set(v___x_2015_, 1, v_k_1990_);
lean_ctor_set(v___x_2015_, 0, v___x_2023_);
v___x_2025_ = v___x_2015_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1990_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1991_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_r_2009_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_r_1993_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___x_2025_);
lean_ctor_set(v___x_2003_, 3, v___y_2020_);
lean_ctor_set(v___x_2003_, 2, v_v_2007_);
lean_ctor_set(v___x_2003_, 1, v_k_2006_);
lean_ctor_set(v___x_2003_, 0, v___x_2018_);
v___x_2027_ = v___x_2003_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_2006_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_2007_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___y_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
v___jp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_nat_add(v___x_2017_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec(v___x_2017_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_l_2008_);
lean_ctor_set(v___x_1982_, 0, v___x_2032_);
v___x_2034_ = v___x_1982_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2038_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2038_, 4, v_l_2008_);
v___x_2034_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_nat_add(v___x_1987_, v_size_2010_);
if (lean_obj_tag(v_r_2009_) == 0)
{
lean_object* v_size_2036_; 
v_size_2036_ = lean_ctor_get(v_r_2009_, 0);
lean_inc(v_size_2036_);
v___y_2020_ = v___x_2034_;
v___y_2021_ = v___x_2035_;
v___y_2022_ = v_size_2036_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_unsigned_to_nat(0u);
v___y_2020_ = v___x_2034_;
v___y_2021_ = v___x_2035_;
v___y_2022_ = v___x_2037_;
goto v___jp_2019_;
}
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
lean_del_object(v___x_1982_);
v___x_2047_ = lean_nat_add(v___x_1987_, v_size_1988_);
v___x_2048_ = lean_nat_add(v___x_2047_, v_size_1989_);
lean_dec(v_size_1989_);
v___x_2049_ = lean_nat_add(v___x_2047_, v_size_2005_);
lean_dec(v___x_2047_);
lean_inc_ref(v_l_1979_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v_l_1992_);
lean_ctor_set(v___x_2003_, 3, v_l_1979_);
lean_ctor_set(v___x_2003_, 2, v_v_1978_);
lean_ctor_set(v___x_2003_, 1, v_k_1977_);
lean_ctor_set(v___x_2003_, 0, v___x_2049_);
v___x_2051_ = v___x_2003_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_l_1992_);
v___x_2051_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_isSharedCheck_2058_ = !lean_is_exclusive(v_l_1979_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; lean_object* v_unused_2063_; 
v_unused_2059_ = lean_ctor_get(v_l_1979_, 4);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_l_1979_, 3);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_l_1979_, 2);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_l_1979_, 1);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_l_1979_, 0);
lean_dec(v_unused_2063_);
v___x_2053_ = v_l_1979_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v_l_1979_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 4, v_r_1993_);
lean_ctor_set(v___x_2053_, 3, v___x_2051_);
lean_ctor_set(v___x_2053_, 2, v_v_1991_);
lean_ctor_set(v___x_2053_, 1, v_k_1990_);
lean_ctor_set(v___x_2053_, 0, v___x_2048_);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_1990_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_1991_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_r_1993_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2071_; 
v_l_2071_ = lean_ctor_get(v_impl_1986_, 3);
lean_inc(v_l_2071_);
if (lean_obj_tag(v_l_2071_) == 0)
{
lean_object* v_r_2072_; lean_object* v_k_2073_; lean_object* v_v_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2097_; 
v_r_2072_ = lean_ctor_get(v_impl_1986_, 4);
v_k_2073_ = lean_ctor_get(v_impl_1986_, 1);
v_v_2074_ = lean_ctor_get(v_impl_1986_, 2);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_impl_1986_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2098_ = lean_ctor_get(v_impl_1986_, 3);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_impl_1986_, 0);
lean_dec(v_unused_2099_);
v___x_2076_ = v_impl_1986_;
v_isShared_2077_ = v_isSharedCheck_2097_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_r_2072_);
lean_inc(v_v_2074_);
lean_inc(v_k_2073_);
lean_dec(v_impl_1986_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2097_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_k_2078_; lean_object* v_v_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2093_; 
v_k_2078_ = lean_ctor_get(v_l_2071_, 1);
v_v_2079_ = lean_ctor_get(v_l_2071_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_l_2071_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_l_2071_, 4);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_l_2071_, 3);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_l_2071_, 0);
lean_dec(v_unused_2096_);
v___x_2081_ = v_l_2071_;
v_isShared_2082_ = v_isSharedCheck_2093_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_v_2079_);
lean_inc(v_k_2078_);
lean_dec(v_l_2071_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2093_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2072_, 2);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v_r_2072_);
lean_ctor_set(v___x_2081_, 3, v_r_2072_);
lean_ctor_set(v___x_2081_, 2, v_v_1978_);
lean_ctor_set(v___x_2081_, 1, v_k_1977_);
lean_ctor_set(v___x_2081_, 0, v___x_1987_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_r_2072_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_r_2072_);
v___x_2085_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2087_; 
lean_inc(v_r_2072_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 3, v_r_2072_);
lean_ctor_set(v___x_2076_, 0, v___x_1987_);
v___x_2087_ = v___x_2076_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_r_2072_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_r_2072_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v___x_2087_);
lean_ctor_set(v___x_1982_, 3, v___x_2085_);
lean_ctor_set(v___x_1982_, 2, v_v_2079_);
lean_ctor_set(v___x_1982_, 1, v_k_2078_);
lean_ctor_set(v___x_1982_, 0, v___x_2083_);
v___x_2089_ = v___x_1982_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v___x_2085_);
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
}
}
}
else
{
lean_object* v_r_2100_; 
v_r_2100_ = lean_ctor_get(v_impl_1986_, 4);
lean_inc(v_r_2100_);
if (lean_obj_tag(v_r_2100_) == 0)
{
lean_object* v_k_2101_; lean_object* v_v_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2113_; 
v_k_2101_ = lean_ctor_get(v_impl_1986_, 1);
v_v_2102_ = lean_ctor_get(v_impl_1986_, 2);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_impl_1986_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2114_ = lean_ctor_get(v_impl_1986_, 4);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_impl_1986_, 3);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_impl_1986_, 0);
lean_dec(v_unused_2116_);
v___x_2104_ = v_impl_1986_;
v_isShared_2105_ = v_isSharedCheck_2113_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
lean_dec(v_impl_1986_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2113_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_unsigned_to_nat(3u);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 4, v_l_2071_);
lean_ctor_set(v___x_2104_, 2, v_v_1978_);
lean_ctor_set(v___x_2104_, 1, v_k_1977_);
lean_ctor_set(v___x_2104_, 0, v___x_1987_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_l_2071_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_l_2071_);
v___x_2108_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_r_2100_);
lean_ctor_set(v___x_1982_, 3, v___x_2108_);
lean_ctor_set(v___x_1982_, 2, v_v_2102_);
lean_ctor_set(v___x_1982_, 1, v_k_2101_);
lean_ctor_set(v___x_1982_, 0, v___x_2106_);
v___x_2110_ = v___x_1982_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_r_2100_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(2u);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_impl_1986_);
lean_ctor_set(v___x_1982_, 3, v_r_2100_);
lean_ctor_set(v___x_1982_, 0, v___x_2117_);
v___x_2119_ = v___x_1982_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_r_2100_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_impl_1986_);
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
else
{
lean_object* v___x_2122_; 
lean_dec(v_v_1978_);
lean_dec(v_k_1977_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 2, v_v_1974_);
lean_ctor_set(v___x_1982_, 1, v_k_1973_);
v___x_2122_ = v___x_1982_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_size_1976_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_k_1973_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_v_1974_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_r_1980_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
lean_object* v_impl_2124_; lean_object* v___x_2125_; 
lean_dec(v_size_1976_);
v_impl_2124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1973_, v_v_1974_, v_l_1979_);
v___x_2125_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1980_) == 0)
{
lean_object* v_size_2126_; lean_object* v_size_2127_; lean_object* v_k_2128_; lean_object* v_v_2129_; lean_object* v_l_2130_; lean_object* v_r_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_size_2126_ = lean_ctor_get(v_r_1980_, 0);
v_size_2127_ = lean_ctor_get(v_impl_2124_, 0);
lean_inc(v_size_2127_);
v_k_2128_ = lean_ctor_get(v_impl_2124_, 1);
lean_inc(v_k_2128_);
v_v_2129_ = lean_ctor_get(v_impl_2124_, 2);
lean_inc(v_v_2129_);
v_l_2130_ = lean_ctor_get(v_impl_2124_, 3);
lean_inc(v_l_2130_);
v_r_2131_ = lean_ctor_get(v_impl_2124_, 4);
lean_inc(v_r_2131_);
v___x_2132_ = lean_unsigned_to_nat(3u);
v___x_2133_ = lean_nat_mul(v___x_2132_, v_size_2126_);
v___x_2134_ = lean_nat_dec_lt(v___x_2133_, v_size_2127_);
lean_dec(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v_r_2131_);
lean_dec(v_l_2130_);
lean_dec(v_v_2129_);
lean_dec(v_k_2128_);
v___x_2135_ = lean_nat_add(v___x_2125_, v_size_2127_);
lean_dec(v_size_2127_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2126_);
lean_dec(v___x_2135_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 3, v_impl_2124_);
lean_ctor_set(v___x_1982_, 0, v___x_2136_);
v___x_2138_ = v___x_1982_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_impl_2124_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_r_1980_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v_impl_2124_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2206_ = lean_ctor_get(v_impl_2124_, 4);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_impl_2124_, 3);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_impl_2124_, 2);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_impl_2124_, 1);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_impl_2124_, 0);
lean_dec(v_unused_2210_);
v___x_2141_ = v_impl_2124_;
v_isShared_2142_ = v_isSharedCheck_2205_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_impl_2124_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2205_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_size_2143_; lean_object* v_size_2144_; lean_object* v_k_2145_; lean_object* v_v_2146_; lean_object* v_l_2147_; lean_object* v_r_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_size_2143_ = lean_ctor_get(v_l_2130_, 0);
v_size_2144_ = lean_ctor_get(v_r_2131_, 0);
v_k_2145_ = lean_ctor_get(v_r_2131_, 1);
v_v_2146_ = lean_ctor_get(v_r_2131_, 2);
v_l_2147_ = lean_ctor_get(v_r_2131_, 3);
v_r_2148_ = lean_ctor_get(v_r_2131_, 4);
v___x_2149_ = lean_unsigned_to_nat(2u);
v___x_2150_ = lean_nat_mul(v___x_2149_, v_size_2143_);
v___x_2151_ = lean_nat_dec_lt(v_size_2144_, v___x_2150_);
lean_dec(v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2180_; 
lean_inc(v_r_2148_);
lean_inc(v_l_2147_);
lean_inc(v_v_2146_);
lean_inc(v_k_2145_);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_r_2131_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2181_ = lean_ctor_get(v_r_2131_, 4);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_r_2131_, 3);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_r_2131_, 2);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_r_2131_, 1);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_r_2131_, 0);
lean_dec(v_unused_2185_);
v___x_2153_ = v_r_2131_;
v_isShared_2154_ = v_isSharedCheck_2180_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v_r_2131_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2180_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___x_2168_; lean_object* v___y_2170_; 
v___x_2155_ = lean_nat_add(v___x_2125_, v_size_2127_);
lean_dec(v_size_2127_);
v___x_2156_ = lean_nat_add(v___x_2155_, v_size_2126_);
lean_dec(v___x_2155_);
v___x_2168_ = lean_nat_add(v___x_2125_, v_size_2143_);
if (lean_obj_tag(v_l_2147_) == 0)
{
lean_object* v_size_2178_; 
v_size_2178_ = lean_ctor_get(v_l_2147_, 0);
lean_inc(v_size_2178_);
v___y_2170_ = v_size_2178_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___y_2170_ = v___x_2179_;
goto v___jp_2169_;
}
v___jp_2157_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_nat_add(v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec(v___y_2159_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 4, v_r_1980_);
lean_ctor_set(v___x_2153_, 3, v_r_2148_);
lean_ctor_set(v___x_2153_, 2, v_v_1978_);
lean_ctor_set(v___x_2153_, 1, v_k_1977_);
lean_ctor_set(v___x_2153_, 0, v___x_2161_);
v___x_2163_ = v___x_2153_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_r_2148_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_r_1980_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2163_);
lean_ctor_set(v___x_2141_, 3, v___y_2158_);
lean_ctor_set(v___x_2141_, 2, v_v_2146_);
lean_ctor_set(v___x_2141_, 1, v_k_2145_);
lean_ctor_set(v___x_2141_, 0, v___x_2156_);
v___x_2165_ = v___x_2141_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_2145_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_2146_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v___y_2158_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_nat_add(v___x_2168_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec(v___x_2168_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_l_2147_);
lean_ctor_set(v___x_1982_, 3, v_l_2130_);
lean_ctor_set(v___x_1982_, 2, v_v_2129_);
lean_ctor_set(v___x_1982_, 1, v_k_2128_);
lean_ctor_set(v___x_1982_, 0, v___x_2171_);
v___x_2173_ = v___x_1982_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2128_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2129_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_l_2130_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_l_2147_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_nat_add(v___x_2125_, v_size_2126_);
if (lean_obj_tag(v_r_2148_) == 0)
{
lean_object* v_size_2175_; 
v_size_2175_ = lean_ctor_get(v_r_2148_, 0);
lean_inc(v_size_2175_);
v___y_2158_ = v___x_2173_;
v___y_2159_ = v___x_2174_;
v___y_2160_ = v_size_2175_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___y_2158_ = v___x_2173_;
v___y_2159_ = v___x_2174_;
v___y_2160_ = v___x_2176_;
goto v___jp_2157_;
}
}
}
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_del_object(v___x_1982_);
v___x_2186_ = lean_nat_add(v___x_2125_, v_size_2127_);
lean_dec(v_size_2127_);
v___x_2187_ = lean_nat_add(v___x_2186_, v_size_2126_);
lean_dec(v___x_2186_);
v___x_2188_ = lean_nat_add(v___x_2125_, v_size_2126_);
v___x_2189_ = lean_nat_add(v___x_2188_, v_size_2144_);
lean_dec(v___x_2188_);
lean_inc_ref(v_r_1980_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_r_1980_);
lean_ctor_set(v___x_2141_, 3, v_r_2131_);
lean_ctor_set(v___x_2141_, 2, v_v_1978_);
lean_ctor_set(v___x_2141_, 1, v_k_1977_);
lean_ctor_set(v___x_2141_, 0, v___x_2189_);
v___x_2191_ = v___x_2141_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_r_2131_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_r_1980_);
v___x_2191_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_isSharedCheck_2198_ = !lean_is_exclusive(v_r_1980_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; lean_object* v_unused_2200_; lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2199_ = lean_ctor_get(v_r_1980_, 4);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_r_1980_, 3);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_r_1980_, 2);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_r_1980_, 1);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_r_1980_, 0);
lean_dec(v_unused_2203_);
v___x_2193_ = v_r_1980_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v_r_1980_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v___x_2191_);
lean_ctor_set(v___x_2193_, 3, v_l_2130_);
lean_ctor_set(v___x_2193_, 2, v_v_2129_);
lean_ctor_set(v___x_2193_, 1, v_k_2128_);
lean_ctor_set(v___x_2193_, 0, v___x_2187_);
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_k_2128_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_v_2129_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_l_2130_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v___x_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2211_; 
v_l_2211_ = lean_ctor_get(v_impl_2124_, 3);
lean_inc(v_l_2211_);
if (lean_obj_tag(v_l_2211_) == 0)
{
lean_object* v_r_2212_; lean_object* v_k_2213_; lean_object* v_v_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2225_; 
v_r_2212_ = lean_ctor_get(v_impl_2124_, 4);
v_k_2213_ = lean_ctor_get(v_impl_2124_, 1);
v_v_2214_ = lean_ctor_get(v_impl_2124_, 2);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_impl_2124_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2226_ = lean_ctor_get(v_impl_2124_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_impl_2124_, 0);
lean_dec(v_unused_2227_);
v___x_2216_ = v_impl_2124_;
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_r_2212_);
lean_inc(v_v_2214_);
lean_inc(v_k_2213_);
lean_dec(v_impl_2124_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2212_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 3, v_r_2212_);
lean_ctor_set(v___x_2216_, 2, v_v_1978_);
lean_ctor_set(v___x_2216_, 1, v_k_1977_);
lean_ctor_set(v___x_2216_, 0, v___x_2125_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_r_2212_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_r_2212_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v___x_2220_);
lean_ctor_set(v___x_1982_, 3, v_l_2211_);
lean_ctor_set(v___x_1982_, 2, v_v_2214_);
lean_ctor_set(v___x_1982_, 1, v_k_2213_);
lean_ctor_set(v___x_1982_, 0, v___x_2218_);
v___x_2222_ = v___x_1982_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2213_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2211_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_r_2228_; 
v_r_2228_ = lean_ctor_get(v_impl_2124_, 4);
lean_inc(v_r_2228_);
if (lean_obj_tag(v_r_2228_) == 0)
{
lean_object* v_k_2229_; lean_object* v_v_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2253_; 
v_k_2229_ = lean_ctor_get(v_impl_2124_, 1);
v_v_2230_ = lean_ctor_get(v_impl_2124_, 2);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_impl_2124_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; 
v_unused_2254_ = lean_ctor_get(v_impl_2124_, 4);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_impl_2124_, 3);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_impl_2124_, 0);
lean_dec(v_unused_2256_);
v___x_2232_ = v_impl_2124_;
v_isShared_2233_ = v_isSharedCheck_2253_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_v_2230_);
lean_inc(v_k_2229_);
lean_dec(v_impl_2124_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2253_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_k_2234_; lean_object* v_v_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2249_; 
v_k_2234_ = lean_ctor_get(v_r_2228_, 1);
v_v_2235_ = lean_ctor_get(v_r_2228_, 2);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_r_2228_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; lean_object* v_unused_2251_; lean_object* v_unused_2252_; 
v_unused_2250_ = lean_ctor_get(v_r_2228_, 4);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_r_2228_, 3);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_r_2228_, 0);
lean_dec(v_unused_2252_);
v___x_2237_ = v_r_2228_;
v_isShared_2238_ = v_isSharedCheck_2249_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_v_2235_);
lean_inc(v_k_2234_);
lean_dec(v_r_2228_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2249_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = lean_unsigned_to_nat(3u);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_l_2211_);
lean_ctor_set(v___x_2237_, 3, v_l_2211_);
lean_ctor_set(v___x_2237_, 2, v_v_2230_);
lean_ctor_set(v___x_2237_, 1, v_k_2229_);
lean_ctor_set(v___x_2237_, 0, v___x_2125_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_k_2229_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_v_2230_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_l_2211_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_l_2211_);
v___x_2241_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 4, v_l_2211_);
lean_ctor_set(v___x_2232_, 2, v_v_1978_);
lean_ctor_set(v___x_2232_, 1, v_k_1977_);
lean_ctor_set(v___x_2232_, 0, v___x_2125_);
v___x_2243_ = v___x_2232_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_l_2211_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_l_2211_);
v___x_2243_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v___x_2243_);
lean_ctor_set(v___x_1982_, 3, v___x_2241_);
lean_ctor_set(v___x_1982_, 2, v_v_2235_);
lean_ctor_set(v___x_1982_, 1, v_k_2234_);
lean_ctor_set(v___x_1982_, 0, v___x_2239_);
v___x_2245_ = v___x_1982_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_unsigned_to_nat(2u);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v_r_2228_);
lean_ctor_set(v___x_1982_, 3, v_impl_2124_);
lean_ctor_set(v___x_1982_, 0, v___x_2257_);
v___x_2259_ = v___x_1982_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_impl_2124_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_r_2228_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_k_1973_);
lean_ctor_set(v___x_2263_, 2, v_v_1974_);
lean_ctor_set(v___x_2263_, 3, v_t_1975_);
lean_ctor_set(v___x_2263_, 4, v_t_1975_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2264_, lean_object* v_x_2265_, size_t v_x_2266_, size_t v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v_cs_2268_; size_t v_j_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_cs_2268_ = lean_ctor_get(v_x_2265_, 0);
v_j_2269_ = lean_usize_shift_right(v_x_2266_, v_x_2267_);
v___x_2270_ = lean_usize_to_nat(v_j_2269_);
v___x_2271_ = lean_array_get_size(v_cs_2268_);
v___x_2272_ = lean_nat_dec_lt(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v___x_2270_);
lean_dec(v_y_2264_);
return v_x_2265_;
}
else
{
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2290_; 
lean_inc_ref(v_cs_2268_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2291_);
v___x_2274_ = v_x_2265_;
v_isShared_2275_ = v_isSharedCheck_2290_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v_x_2265_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2290_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v_i_2279_; size_t v___x_2280_; size_t v_shift_2281_; lean_object* v_v_2282_; lean_object* v___x_2283_; lean_object* v_xs_x27_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_shift_left(v___x_2276_, v_x_2267_);
v___x_2278_ = lean_usize_sub(v___x_2277_, v___x_2276_);
v_i_2279_ = lean_usize_land(v_x_2266_, v___x_2278_);
v___x_2280_ = ((size_t)5ULL);
v_shift_2281_ = lean_usize_sub(v_x_2267_, v___x_2280_);
v_v_2282_ = lean_array_fget(v_cs_2268_, v___x_2270_);
v___x_2283_ = lean_box(0);
v_xs_x27_2284_ = lean_array_fset(v_cs_2268_, v___x_2270_, v___x_2283_);
v___x_2285_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2264_, v_v_2282_, v_i_2279_, v_shift_2281_);
v___x_2286_ = lean_array_fset(v_xs_x27_2284_, v___x_2270_, v___x_2285_);
lean_dec(v___x_2270_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2286_);
v___x_2288_ = v___x_2274_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_vs_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_vs_2292_ = lean_ctor_get(v_x_2265_, 0);
v___x_2293_ = lean_usize_to_nat(v_x_2266_);
v___x_2294_ = lean_array_get_size(v_vs_2292_);
v___x_2295_ = lean_nat_dec_lt(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_dec(v___x_2293_);
lean_dec(v_y_2264_);
return v_x_2265_;
}
else
{
lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2310_; 
lean_inc_ref(v_vs_2292_);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2311_);
v___x_2297_ = v_x_2265_;
v_isShared_2298_ = v_isSharedCheck_2310_;
goto v_resetjp_2296_;
}
else
{
lean_dec(v_x_2265_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2310_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_v_2299_; lean_object* v___x_2300_; lean_object* v_xs_x27_2301_; lean_object* v___y_2303_; uint8_t v___x_2308_; 
v_v_2299_ = lean_array_fget(v_vs_2292_, v___x_2293_);
v___x_2300_ = lean_box(0);
v_xs_x27_2301_ = lean_array_fset(v_vs_2292_, v___x_2293_, v___x_2300_);
v___x_2308_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2264_, v_v_2299_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2264_, v___x_2300_, v_v_2299_);
v___y_2303_ = v___x_2309_;
goto v___jp_2302_;
}
else
{
lean_dec(v_y_2264_);
v___y_2303_ = v_v_2299_;
goto v___jp_2302_;
}
v___jp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_array_fset(v_xs_x27_2301_, v___x_2293_, v___y_2303_);
lean_dec(v___x_2293_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2304_);
v___x_2306_ = v___x_2297_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
size_t v_x_6038__boxed_2316_; size_t v_x_6039__boxed_2317_; lean_object* v_res_2318_; 
v_x_6038__boxed_2316_ = lean_unbox_usize(v_x_2314_);
lean_dec(v_x_2314_);
v_x_6039__boxed_2317_ = lean_unbox_usize(v_x_2315_);
lean_dec(v_x_2315_);
v_res_2318_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2312_, v_x_2313_, v_x_6038__boxed_2316_, v_x_6039__boxed_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2319_, lean_object* v_t_2320_, lean_object* v_i_2321_){
_start:
{
lean_object* v_root_2322_; lean_object* v_tail_2323_; lean_object* v_size_2324_; size_t v_shift_2325_; lean_object* v_tailOff_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2353_; 
v_root_2322_ = lean_ctor_get(v_t_2320_, 0);
v_tail_2323_ = lean_ctor_get(v_t_2320_, 1);
v_size_2324_ = lean_ctor_get(v_t_2320_, 2);
v_shift_2325_ = lean_ctor_get_usize(v_t_2320_, 4);
v_tailOff_2326_ = lean_ctor_get(v_t_2320_, 3);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_t_2320_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2328_ = v_t_2320_;
v_isShared_2329_ = v_isSharedCheck_2353_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_tailOff_2326_);
lean_inc(v_size_2324_);
lean_inc(v_tail_2323_);
lean_inc(v_root_2322_);
lean_dec(v_t_2320_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2353_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_nat_dec_le(v_tailOff_2326_, v_i_2321_);
if (v___x_2330_ == 0)
{
size_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_usize_of_nat(v_i_2321_);
v___x_2332_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2319_, v_root_2322_, v___x_2331_, v_shift_2325_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_tail_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_size_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_tailOff_2326_);
lean_ctor_set_usize(v_reuseFailAlloc_2335_, 4, v_shift_2325_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2336_ = lean_nat_sub(v_i_2321_, v_tailOff_2326_);
v___x_2337_ = lean_array_get_size(v_tail_2323_);
v___x_2338_ = lean_nat_dec_lt(v___x_2336_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v___x_2336_);
lean_dec(v_y_2319_);
if (v_isShared_2329_ == 0)
{
v___x_2340_ = v___x_2328_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_root_2322_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_tail_2323_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_size_2324_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_tailOff_2326_);
lean_ctor_set_usize(v_reuseFailAlloc_2341_, 4, v_shift_2325_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v_v_2342_; lean_object* v___x_2343_; lean_object* v_xs_x27_2344_; lean_object* v___y_2346_; uint8_t v___x_2351_; 
v_v_2342_ = lean_array_fget(v_tail_2323_, v___x_2336_);
v___x_2343_ = lean_box(0);
v_xs_x27_2344_ = lean_array_fset(v_tail_2323_, v___x_2336_, v___x_2343_);
v___x_2351_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2319_, v_v_2342_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2319_, v___x_2343_, v_v_2342_);
v___y_2346_ = v___x_2352_;
goto v___jp_2345_;
}
else
{
lean_dec(v_y_2319_);
v___y_2346_ = v_v_2342_;
goto v___jp_2345_;
}
v___jp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = lean_array_fset(v_xs_x27_2344_, v___x_2336_, v___y_2346_);
lean_dec(v___x_2336_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2347_);
v___x_2349_ = v___x_2328_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_root_2322_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_size_2324_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_tailOff_2326_);
lean_ctor_set_usize(v_reuseFailAlloc_2350_, 4, v_shift_2325_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2354_, lean_object* v_t_2355_, lean_object* v_i_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2354_, v_t_2355_, v_i_2356_);
lean_dec(v_i_2356_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2358_, lean_object* v_y_2359_, lean_object* v_x_2360_, lean_object* v_s_2361_){
_start:
{
lean_object* v_structs_2362_; lean_object* v_typeIdOf_2363_; lean_object* v_exprToStructId_2364_; lean_object* v_exprToStructIdEntries_2365_; lean_object* v_forbiddenNatModules_2366_; lean_object* v_natStructs_2367_; lean_object* v_natTypeIdOf_2368_; lean_object* v_exprToNatStructId_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_structs_2362_ = lean_ctor_get(v_s_2361_, 0);
v_typeIdOf_2363_ = lean_ctor_get(v_s_2361_, 1);
v_exprToStructId_2364_ = lean_ctor_get(v_s_2361_, 2);
v_exprToStructIdEntries_2365_ = lean_ctor_get(v_s_2361_, 3);
v_forbiddenNatModules_2366_ = lean_ctor_get(v_s_2361_, 4);
v_natStructs_2367_ = lean_ctor_get(v_s_2361_, 5);
v_natTypeIdOf_2368_ = lean_ctor_get(v_s_2361_, 6);
v_exprToNatStructId_2369_ = lean_ctor_get(v_s_2361_, 7);
v___x_2370_ = lean_array_get_size(v_structs_2362_);
v___x_2371_ = lean_nat_dec_lt(v_a_2358_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec(v_y_2359_);
return v_s_2361_;
}
else
{
lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2433_; 
lean_inc_ref(v_exprToNatStructId_2369_);
lean_inc_ref(v_natTypeIdOf_2368_);
lean_inc_ref(v_natStructs_2367_);
lean_inc_ref(v_forbiddenNatModules_2366_);
lean_inc_ref(v_exprToStructIdEntries_2365_);
lean_inc_ref(v_exprToStructId_2364_);
lean_inc_ref(v_typeIdOf_2363_);
lean_inc_ref(v_structs_2362_);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_s_2361_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; lean_object* v_unused_2441_; 
v_unused_2434_ = lean_ctor_get(v_s_2361_, 7);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_s_2361_, 6);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_s_2361_, 5);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_s_2361_, 4);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_s_2361_, 3);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_s_2361_, 2);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_s_2361_, 1);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_s_2361_, 0);
lean_dec(v_unused_2441_);
v___x_2373_ = v_s_2361_;
v_isShared_2374_ = v_isSharedCheck_2433_;
goto v_resetjp_2372_;
}
else
{
lean_dec(v_s_2361_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2433_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v_v_2375_; lean_object* v_id_2376_; lean_object* v_ringId_x3f_2377_; lean_object* v_type_2378_; lean_object* v_u_2379_; lean_object* v_intModuleInst_2380_; lean_object* v_leInst_x3f_2381_; lean_object* v_ltInst_x3f_2382_; lean_object* v_lawfulOrderLTInst_x3f_2383_; lean_object* v_isPreorderInst_x3f_2384_; lean_object* v_orderedAddInst_x3f_2385_; lean_object* v_isLinearInst_x3f_2386_; lean_object* v_noNatDivInst_x3f_2387_; lean_object* v_ringInst_x3f_2388_; lean_object* v_commRingInst_x3f_2389_; lean_object* v_orderedRingInst_x3f_2390_; lean_object* v_fieldInst_x3f_2391_; lean_object* v_charInst_x3f_2392_; lean_object* v_zero_2393_; lean_object* v_ofNatZero_2394_; lean_object* v_one_x3f_2395_; lean_object* v_leFn_x3f_2396_; lean_object* v_ltFn_x3f_2397_; lean_object* v_addFn_2398_; lean_object* v_zsmulFn_2399_; lean_object* v_nsmulFn_2400_; lean_object* v_zsmulFn_x3f_2401_; lean_object* v_nsmulFn_x3f_2402_; lean_object* v_homomulFn_x3f_2403_; lean_object* v_subFn_2404_; lean_object* v_negFn_2405_; lean_object* v_vars_2406_; lean_object* v_varMap_2407_; lean_object* v_lowers_2408_; lean_object* v_uppers_2409_; lean_object* v_diseqs_2410_; lean_object* v_assignment_2411_; uint8_t v_caseSplits_2412_; lean_object* v_conflict_x3f_2413_; lean_object* v_diseqSplits_2414_; lean_object* v_elimEqs_2415_; lean_object* v_elimStack_2416_; lean_object* v_occurs_2417_; lean_object* v_ignored_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2432_; 
v_v_2375_ = lean_array_fget(v_structs_2362_, v_a_2358_);
v_id_2376_ = lean_ctor_get(v_v_2375_, 0);
v_ringId_x3f_2377_ = lean_ctor_get(v_v_2375_, 1);
v_type_2378_ = lean_ctor_get(v_v_2375_, 2);
v_u_2379_ = lean_ctor_get(v_v_2375_, 3);
v_intModuleInst_2380_ = lean_ctor_get(v_v_2375_, 4);
v_leInst_x3f_2381_ = lean_ctor_get(v_v_2375_, 5);
v_ltInst_x3f_2382_ = lean_ctor_get(v_v_2375_, 6);
v_lawfulOrderLTInst_x3f_2383_ = lean_ctor_get(v_v_2375_, 7);
v_isPreorderInst_x3f_2384_ = lean_ctor_get(v_v_2375_, 8);
v_orderedAddInst_x3f_2385_ = lean_ctor_get(v_v_2375_, 9);
v_isLinearInst_x3f_2386_ = lean_ctor_get(v_v_2375_, 10);
v_noNatDivInst_x3f_2387_ = lean_ctor_get(v_v_2375_, 11);
v_ringInst_x3f_2388_ = lean_ctor_get(v_v_2375_, 12);
v_commRingInst_x3f_2389_ = lean_ctor_get(v_v_2375_, 13);
v_orderedRingInst_x3f_2390_ = lean_ctor_get(v_v_2375_, 14);
v_fieldInst_x3f_2391_ = lean_ctor_get(v_v_2375_, 15);
v_charInst_x3f_2392_ = lean_ctor_get(v_v_2375_, 16);
v_zero_2393_ = lean_ctor_get(v_v_2375_, 17);
v_ofNatZero_2394_ = lean_ctor_get(v_v_2375_, 18);
v_one_x3f_2395_ = lean_ctor_get(v_v_2375_, 19);
v_leFn_x3f_2396_ = lean_ctor_get(v_v_2375_, 20);
v_ltFn_x3f_2397_ = lean_ctor_get(v_v_2375_, 21);
v_addFn_2398_ = lean_ctor_get(v_v_2375_, 22);
v_zsmulFn_2399_ = lean_ctor_get(v_v_2375_, 23);
v_nsmulFn_2400_ = lean_ctor_get(v_v_2375_, 24);
v_zsmulFn_x3f_2401_ = lean_ctor_get(v_v_2375_, 25);
v_nsmulFn_x3f_2402_ = lean_ctor_get(v_v_2375_, 26);
v_homomulFn_x3f_2403_ = lean_ctor_get(v_v_2375_, 27);
v_subFn_2404_ = lean_ctor_get(v_v_2375_, 28);
v_negFn_2405_ = lean_ctor_get(v_v_2375_, 29);
v_vars_2406_ = lean_ctor_get(v_v_2375_, 30);
v_varMap_2407_ = lean_ctor_get(v_v_2375_, 31);
v_lowers_2408_ = lean_ctor_get(v_v_2375_, 32);
v_uppers_2409_ = lean_ctor_get(v_v_2375_, 33);
v_diseqs_2410_ = lean_ctor_get(v_v_2375_, 34);
v_assignment_2411_ = lean_ctor_get(v_v_2375_, 35);
v_caseSplits_2412_ = lean_ctor_get_uint8(v_v_2375_, sizeof(void*)*42);
v_conflict_x3f_2413_ = lean_ctor_get(v_v_2375_, 36);
v_diseqSplits_2414_ = lean_ctor_get(v_v_2375_, 37);
v_elimEqs_2415_ = lean_ctor_get(v_v_2375_, 38);
v_elimStack_2416_ = lean_ctor_get(v_v_2375_, 39);
v_occurs_2417_ = lean_ctor_get(v_v_2375_, 40);
v_ignored_2418_ = lean_ctor_get(v_v_2375_, 41);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_v_2375_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2420_ = v_v_2375_;
v_isShared_2421_ = v_isSharedCheck_2432_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_ignored_2418_);
lean_inc(v_occurs_2417_);
lean_inc(v_elimStack_2416_);
lean_inc(v_elimEqs_2415_);
lean_inc(v_diseqSplits_2414_);
lean_inc(v_conflict_x3f_2413_);
lean_inc(v_assignment_2411_);
lean_inc(v_diseqs_2410_);
lean_inc(v_uppers_2409_);
lean_inc(v_lowers_2408_);
lean_inc(v_varMap_2407_);
lean_inc(v_vars_2406_);
lean_inc(v_negFn_2405_);
lean_inc(v_subFn_2404_);
lean_inc(v_homomulFn_x3f_2403_);
lean_inc(v_nsmulFn_x3f_2402_);
lean_inc(v_zsmulFn_x3f_2401_);
lean_inc(v_nsmulFn_2400_);
lean_inc(v_zsmulFn_2399_);
lean_inc(v_addFn_2398_);
lean_inc(v_ltFn_x3f_2397_);
lean_inc(v_leFn_x3f_2396_);
lean_inc(v_one_x3f_2395_);
lean_inc(v_ofNatZero_2394_);
lean_inc(v_zero_2393_);
lean_inc(v_charInst_x3f_2392_);
lean_inc(v_fieldInst_x3f_2391_);
lean_inc(v_orderedRingInst_x3f_2390_);
lean_inc(v_commRingInst_x3f_2389_);
lean_inc(v_ringInst_x3f_2388_);
lean_inc(v_noNatDivInst_x3f_2387_);
lean_inc(v_isLinearInst_x3f_2386_);
lean_inc(v_orderedAddInst_x3f_2385_);
lean_inc(v_isPreorderInst_x3f_2384_);
lean_inc(v_lawfulOrderLTInst_x3f_2383_);
lean_inc(v_ltInst_x3f_2382_);
lean_inc(v_leInst_x3f_2381_);
lean_inc(v_intModuleInst_2380_);
lean_inc(v_u_2379_);
lean_inc(v_type_2378_);
lean_inc(v_ringId_x3f_2377_);
lean_inc(v_id_2376_);
lean_dec(v_v_2375_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2432_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v_xs_x27_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2422_ = lean_box(0);
v_xs_x27_2423_ = lean_array_fset(v_structs_2362_, v_a_2358_, v___x_2422_);
v___x_2424_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2359_, v_occurs_2417_, v_x_2360_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 40, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_id_2376_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_ringId_x3f_2377_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_type_2378_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_u_2379_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_intModuleInst_2380_);
lean_ctor_set(v_reuseFailAlloc_2431_, 5, v_leInst_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2431_, 6, v_ltInst_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2431_, 7, v_lawfulOrderLTInst_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2431_, 8, v_isPreorderInst_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2431_, 9, v_orderedAddInst_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2431_, 10, v_isLinearInst_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2431_, 11, v_noNatDivInst_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2431_, 12, v_ringInst_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2431_, 13, v_commRingInst_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2431_, 14, v_orderedRingInst_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2431_, 15, v_fieldInst_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2431_, 16, v_charInst_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2431_, 17, v_zero_2393_);
lean_ctor_set(v_reuseFailAlloc_2431_, 18, v_ofNatZero_2394_);
lean_ctor_set(v_reuseFailAlloc_2431_, 19, v_one_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2431_, 20, v_leFn_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2431_, 21, v_ltFn_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2431_, 22, v_addFn_2398_);
lean_ctor_set(v_reuseFailAlloc_2431_, 23, v_zsmulFn_2399_);
lean_ctor_set(v_reuseFailAlloc_2431_, 24, v_nsmulFn_2400_);
lean_ctor_set(v_reuseFailAlloc_2431_, 25, v_zsmulFn_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2431_, 26, v_nsmulFn_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2431_, 27, v_homomulFn_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2431_, 28, v_subFn_2404_);
lean_ctor_set(v_reuseFailAlloc_2431_, 29, v_negFn_2405_);
lean_ctor_set(v_reuseFailAlloc_2431_, 30, v_vars_2406_);
lean_ctor_set(v_reuseFailAlloc_2431_, 31, v_varMap_2407_);
lean_ctor_set(v_reuseFailAlloc_2431_, 32, v_lowers_2408_);
lean_ctor_set(v_reuseFailAlloc_2431_, 33, v_uppers_2409_);
lean_ctor_set(v_reuseFailAlloc_2431_, 34, v_diseqs_2410_);
lean_ctor_set(v_reuseFailAlloc_2431_, 35, v_assignment_2411_);
lean_ctor_set(v_reuseFailAlloc_2431_, 36, v_conflict_x3f_2413_);
lean_ctor_set(v_reuseFailAlloc_2431_, 37, v_diseqSplits_2414_);
lean_ctor_set(v_reuseFailAlloc_2431_, 38, v_elimEqs_2415_);
lean_ctor_set(v_reuseFailAlloc_2431_, 39, v_elimStack_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 40, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2431_, 41, v_ignored_2418_);
lean_ctor_set_uint8(v_reuseFailAlloc_2431_, sizeof(void*)*42, v_caseSplits_2412_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_array_fset(v_xs_x27_2423_, v_a_2358_, v___x_2426_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2427_);
v___x_2429_ = v___x_2373_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_typeIdOf_2363_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_exprToStructId_2364_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_exprToStructIdEntries_2365_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_forbiddenNatModules_2366_);
lean_ctor_set(v_reuseFailAlloc_2430_, 5, v_natStructs_2367_);
lean_ctor_set(v_reuseFailAlloc_2430_, 6, v_natTypeIdOf_2368_);
lean_ctor_set(v_reuseFailAlloc_2430_, 7, v_exprToNatStructId_2369_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2442_, lean_object* v_y_2443_, lean_object* v_x_2444_, lean_object* v_s_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2442_, v_y_2443_, v_x_2444_, v_s_2445_);
lean_dec(v_x_2444_);
lean_dec(v_a_2442_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2447_, lean_object* v_y_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2447_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2474_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2474_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2474_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
uint8_t v___x_2466_; 
v___x_2466_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2448_, v_a_2462_);
lean_dec(v_a_2462_);
if (v___x_2466_ == 0)
{
lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_del_object(v___x_2464_);
lean_inc(v_a_2449_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2467_, 0, v_a_2449_);
lean_closure_set(v___f_2467_, 1, v_y_2448_);
lean_closure_set(v___f_2467_, 2, v_x_2447_);
v___x_2468_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2469_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2468_, v___f_2467_, v_a_2450_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v_y_2448_);
lean_dec(v_x_2447_);
v___x_2470_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2470_);
v___x_2472_ = v___x_2464_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_y_2448_);
lean_dec(v_x_2447_);
v_a_2475_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2461_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2461_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2483_, lean_object* v_y_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2483_, v_y_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec(v_a_2485_);
return v_res_2497_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2498_, lean_object* v_k_2499_, lean_object* v_t_2500_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2499_, v_t_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2502_, lean_object* v_k_2503_, lean_object* v_t_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2502_, v_k_2503_, v_t_2504_);
lean_dec(v_t_2504_);
lean_dec(v_k_2503_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2507_, lean_object* v_k_2508_, lean_object* v_v_2509_, lean_object* v_t_2510_, lean_object* v_hl_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2508_, v_v_2509_, v_t_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2513_, lean_object* v_p_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
if (lean_obj_tag(v_p_2514_) == 1)
{
lean_object* v_v_2527_; lean_object* v_p_2528_; lean_object* v___x_2529_; 
v_v_2527_ = lean_ctor_get(v_p_2514_, 1);
lean_inc(v_v_2527_);
v_p_2528_ = lean_ctor_get(v_p_2514_, 2);
lean_inc(v_p_2528_);
lean_dec_ref(v_p_2514_);
lean_inc(v_y_2513_);
v___x_2529_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2527_, v_y_2513_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_dec_ref(v___x_2529_);
v_p_2514_ = v_p_2528_;
goto _start;
}
else
{
lean_dec(v_p_2528_);
lean_dec(v_y_2513_);
return v___x_2529_;
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_p_2514_);
lean_dec(v_y_2513_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2533_, lean_object* v_p_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2533_, v_p_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_a_2535_);
return v_res_2547_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
if (lean_obj_tag(v_p_2551_) == 1)
{
lean_object* v_v_2564_; lean_object* v_p_2565_; lean_object* v___x_2566_; 
v_v_2564_ = lean_ctor_get(v_p_2551_, 1);
lean_inc(v_v_2564_);
v_p_2565_ = lean_ctor_get(v_p_2551_, 2);
lean_inc(v_p_2565_);
lean_dec_ref(v_p_2551_);
v___x_2566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2564_, v_p_2565_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2566_;
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_p_2551_);
v___x_2567_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2568_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2567_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec(v_a_2570_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
if (lean_obj_tag(v_p_2583_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
else
{
lean_object* v_k_2598_; lean_object* v_v_2599_; lean_object* v_p_2600_; lean_object* v___x_2601_; 
v_k_2598_ = lean_ctor_get(v_p_2583_, 0);
v_v_2599_ = lean_ctor_get(v_p_2583_, 1);
v_p_2600_ = lean_ctor_get(v_p_2583_, 2);
v___x_2601_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2628_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2628_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2628_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___y_2607_; lean_object* v_elimEqs_2622_; lean_object* v_size_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v_elimEqs_2622_ = lean_ctor_get(v_a_2602_, 38);
lean_inc_ref(v_elimEqs_2622_);
lean_dec(v_a_2602_);
v_size_2623_ = lean_ctor_get(v_elimEqs_2622_, 2);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_nat_dec_lt(v_v_2599_, v_size_2623_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v_elimEqs_2622_);
v___x_2626_ = l_outOfBounds___redArg(v___x_2624_);
v___y_2607_ = v___x_2626_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2624_, v_elimEqs_2622_, v_v_2599_);
lean_dec_ref(v_elimEqs_2622_);
v___y_2607_ = v___x_2627_;
goto v___jp_2606_;
}
v___jp_2606_:
{
if (lean_obj_tag(v___y_2607_) == 1)
{
lean_object* v_val_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2620_; 
v_val_2608_ = lean_ctor_get(v___y_2607_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___y_2607_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2610_ = v___y_2607_;
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_val_2608_);
lean_dec(v___y_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2620_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_inc(v_v_2599_);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_v_2599_);
lean_ctor_set(v___x_2612_, 1, v_val_2608_);
lean_inc(v_k_2598_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_k_2598_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2613_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2615_);
v___x_2617_ = v___x_2604_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_dec(v___y_2607_);
lean_del_object(v___x_2604_);
v_p_2583_ = v_p_2600_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
v_a_2629_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2601_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2601_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_p_2637_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 0)
{
return v_x_2652_;
}
else
{
lean_object* v_k_2653_; lean_object* v_p_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_k_2653_ = lean_ctor_get(v_x_2651_, 0);
v_p_2654_ = lean_ctor_get(v_x_2651_, 2);
v___x_2655_ = lean_nat_to_int(v_x_2652_);
v___x_2656_ = l_Int_gcd(v_k_2653_, v___x_2655_);
lean_dec(v___x_2655_);
v_x_2651_ = v_p_2654_;
v_x_2652_ = v___x_2656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2658_, v_x_2659_);
lean_dec(v_x_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2661_){
_start:
{
if (lean_obj_tag(v_p_2661_) == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
return v___x_2662_;
}
else
{
lean_object* v_k_2663_; lean_object* v_p_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_k_2663_ = lean_ctor_get(v_p_2661_, 0);
v_p_2664_ = lean_ctor_get(v_p_2661_, 2);
v___x_2665_ = lean_nat_abs(v_k_2663_);
v___x_2666_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2664_, v___x_2665_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2667_);
lean_dec(v_p_2667_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2669_, lean_object* v_k_2670_){
_start:
{
if (lean_obj_tag(v_p_2669_) == 0)
{
return v_p_2669_;
}
else
{
lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v_p_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2682_; 
v_k_2671_ = lean_ctor_get(v_p_2669_, 0);
v_v_2672_ = lean_ctor_get(v_p_2669_, 1);
v_p_2673_ = lean_ctor_get(v_p_2669_, 2);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_p_2669_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2675_ = v_p_2669_;
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_p_2673_);
lean_inc(v_v_2672_);
lean_inc(v_k_2671_);
lean_dec(v_p_2669_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_int_ediv(v_k_2671_, v_k_2670_);
lean_dec(v_k_2671_);
v___x_2678_ = l_Lean_Grind_Linarith_Poly_div(v_p_2673_, v_k_2670_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 2, v___x_2678_);
lean_ctor_set(v___x_2675_, 0, v___x_2677_);
v___x_2680_ = v___x_2675_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_v_2672_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v___x_2678_);
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
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2683_, lean_object* v_k_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Grind_Linarith_Poly_div(v_p_2683_, v_k_2684_);
lean_dec(v_k_2684_);
return v_res_2685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_to_int(v___x_2686_);
return v___x_2687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2689_ = lean_int_neg(v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2690_, lean_object* v_x_2691_, lean_object* v_p_2692_){
_start:
{
uint8_t v___y_2694_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2706_ = lean_int_dec_eq(v_k_2690_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2708_ = lean_int_dec_eq(v_k_2690_, v___x_2707_);
v___y_2694_ = v___x_2708_;
goto v___jp_2693_;
}
else
{
v___y_2694_ = v___x_2706_;
goto v___jp_2693_;
}
v___jp_2693_:
{
if (v___y_2694_ == 0)
{
if (lean_obj_tag(v_p_2692_) == 0)
{
lean_object* v___x_2695_; 
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_k_2690_);
lean_ctor_set(v___x_2695_, 1, v_x_2691_);
return v___x_2695_;
}
else
{
lean_object* v_k_2696_; lean_object* v_v_2697_; lean_object* v_p_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v_k_2696_ = lean_ctor_get(v_p_2692_, 0);
lean_inc(v_k_2696_);
v_v_2697_ = lean_ctor_get(v_p_2692_, 1);
lean_inc(v_v_2697_);
v_p_2698_ = lean_ctor_get(v_p_2692_, 2);
lean_inc(v_p_2698_);
lean_dec_ref(v_p_2692_);
v___x_2699_ = lean_nat_abs(v_k_2696_);
v___x_2700_ = lean_nat_abs(v_k_2690_);
v___x_2701_ = lean_nat_dec_lt(v___x_2699_, v___x_2700_);
lean_dec(v___x_2700_);
lean_dec(v___x_2699_);
if (v___x_2701_ == 0)
{
lean_dec(v_v_2697_);
lean_dec(v_k_2696_);
v_p_2692_ = v_p_2698_;
goto _start;
}
else
{
lean_dec(v_x_2691_);
lean_dec(v_k_2690_);
v_k_2690_ = v_k_2696_;
v_x_2691_ = v_v_2697_;
v_p_2692_ = v_p_2698_;
goto _start;
}
}
}
else
{
lean_object* v___x_2704_; 
lean_dec(v_p_2692_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_k_2690_);
lean_ctor_set(v___x_2704_, 1, v_x_2691_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2709_){
_start:
{
if (lean_obj_tag(v_p_2709_) == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_box(0);
return v___x_2710_;
}
else
{
lean_object* v_k_2711_; lean_object* v_v_2712_; lean_object* v_p_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_k_2711_ = lean_ctor_get(v_p_2709_, 0);
lean_inc(v_k_2711_);
v_v_2712_ = lean_ctor_get(v_p_2709_, 1);
lean_inc(v_v_2712_);
v_p_2713_ = lean_ctor_get(v_p_2709_, 2);
lean_inc(v_p_2713_);
lean_dec_ref(v_p_2709_);
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2711_, v_v_2712_, v_p_2713_);
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
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
