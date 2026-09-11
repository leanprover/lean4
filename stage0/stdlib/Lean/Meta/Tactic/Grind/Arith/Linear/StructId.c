// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Insts import Init.Grind.Module.Envelope
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "`grind linarith` expected"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nto be definitionally equal to"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toIntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 160, 55, 74, 32, 205, 206, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "type has a `Preorder` and is a `Semiring`, but is not an ordered ring, failed to synthesize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "NoNatZeroDivisors"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 29, 6, 12, 7, 77, 98, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value),LEAN_SCALAR_PTR_LITERAL(75, 224, 25, 76, 51, 82, 222, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toAddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(205, 72, 3, 192, 99, 106, 67, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "AddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toAddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(143, 195, 31, 215, 150, 195, 138, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__65_value),LEAN_SCALAR_PTR_LITERAL(93, 134, 71, 250, 19, 181, 172, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ofNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 244, 42, 211, 144, 181, 88, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(28, 233, 202, 97, 203, 184, 134, 106)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(124, 125, 226, 15, 218, 207, 24, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toOfNat0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(208, 59, 186, 84, 178, 224, 2, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(28, 233, 202, 97, 203, 184, 134, 106)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(85, 115, 161, 225, 76, 32, 159, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(220, 51, 153, 189, 12, 154, 25, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_value),LEAN_SCALAR_PTR_LITERAL(144, 111, 86, 72, 218, 93, 29, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(245, 167, 193, 225, 213, 13, 125, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(168, 238, 174, 79, 173, 177, 80, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(89, 64, 142, 19, 104, 31, 117, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instIsLinearOrderQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(230, 87, 230, 220, 201, 183, 231, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instLEQOfOrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(161, 134, 150, 210, 182, 168, 122, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instLTQOfOrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(159, 207, 2, 71, 208, 154, 4, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instIsPreorderQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(189, 25, 119, 3, 206, 38, 180, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instOrderedAddQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(120, 114, 202, 218, 72, 0, 10, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instLawfulOrderLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(161, 160, 205, 130, 233, 12, 158, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(64, 237, 13, 63, 87, 160, 117, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 228, 118, 74, 233, 69, 129, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(lean_object* v_e_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_canon(v_e_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = l_Lean_Meta_Sym_shareCommon(v_a_10_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
return v___x_11_;
}
else
{
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg___boxed(lean_object* v_e_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_e_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
lean_dec(v_a_18_);
lean_dec_ref(v_a_17_);
lean_dec(v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec_ref(v_a_13_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(lean_object* v_e_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_e_21_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___boxed(lean_object* v_e_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess(v_e_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec(v_a_35_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(lean_object* v_fn_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_fn_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg___boxed(lean_object* v_fn_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___redArg(v_fn_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(lean_object* v_fn_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_fn_65_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn___boxed(lean_object* v_fn_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeFn(v_fn_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(lean_object* v_c_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v_c_91_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_n(v_a_104_, 2);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_box(0);
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
lean_inc(v_a_97_);
lean_inc_ref(v_a_96_);
lean_inc(v_a_95_);
lean_inc_ref(v_a_94_);
lean_inc(v_a_93_);
lean_inc(v_a_92_);
v___x_107_ = lean_grind_internalize(v_a_104_, v___x_105_, v___x_106_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v___x_107_, 0);
lean_dec(v_unused_115_);
v___x_109_ = v___x_107_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_dec(v___x_107_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v_a_104_);
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_104_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_a_104_);
v_a_116_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_107_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_107_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst___boxed(lean_object* v_c_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocessConst(v_c_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec(v_a_125_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(lean_object* v_c_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Sym_canon(v_c_137_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_151_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = l_Lean_Meta_Sym_shareCommon(v_a_150_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_n(v_a_152_, 2);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_box(0);
lean_inc(v_a_147_);
lean_inc_ref(v_a_146_);
lean_inc(v_a_145_);
lean_inc_ref(v_a_144_);
lean_inc(v_a_143_);
lean_inc_ref(v_a_142_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_a_139_);
lean_inc(v_a_138_);
v___x_155_ = lean_grind_internalize(v_a_152_, v___x_153_, v___x_154_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_155_, 0);
lean_dec(v_unused_163_);
v___x_157_ = v___x_155_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_dec(v___x_155_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v_a_152_);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_152_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_152_);
v_a_164_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_155_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_155_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
return v___x_151_;
}
}
else
{
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst___boxed(lean_object* v_c_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v_c_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec(v_a_173_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__0));
v___x_187_ = l_Lean_stringToMessageData(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__2));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__1);
v___x_195_ = l_Lean_indentExpr(v_a_191_);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___closed__3);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_indentExpr(v_b_192_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg___boxed(lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_202_, v_b_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(lean_object* v_a_206_, lean_object* v_b_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_206_, v_b_207_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___boxed(lean_object* v_a_214_, lean_object* v_b_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg(v_a_214_, v_b_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(lean_object* v_msgData_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; lean_object* v_toCold_231_; lean_object* v_mctx_232_; lean_object* v_lctx_233_; lean_object* v_options_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = lean_st_ref_get(v___y_224_);
v_toCold_231_ = lean_ctor_get(v___y_225_, 0);
v_mctx_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_mctx_232_);
lean_dec(v___x_230_);
v_lctx_233_ = lean_ctor_get(v___y_223_, 2);
v_options_234_ = lean_ctor_get(v_toCold_231_, 2);
lean_inc_ref(v_options_234_);
lean_inc_ref(v_lctx_233_);
v___x_235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_235_, 0, v_env_229_);
lean_ctor_set(v___x_235_, 1, v_mctx_232_);
lean_ctor_set(v___x_235_, 2, v_lctx_233_);
lean_ctor_set(v___x_235_, 3, v_options_234_);
v___x_236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_msgData_222_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_ref_251_; lean_object* v___x_252_; lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_ref_251_ = lean_ctor_get(v___y_248_, 2);
v___x_252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_inc(v_ref_251_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_ref_251_);
lean_ctor_set(v___x_257_, 1, v_a_253_);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 1);
lean_ctor_set(v___x_255_, 0, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
lean_inc_ref(v_b_270_);
lean_inc_ref(v_a_269_);
v___x_276_ = l_Lean_Meta_isDefEqD(v_a_269_, v_b_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_unbox(v_a_277_);
lean_dec(v_a_277_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v_a_283_; lean_object* v___x_284_; 
lean_del_object(v___x_279_);
v___x_282_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_269_, v_b_270_);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
v___x_284_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_a_283_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec_ref(v_b_270_);
lean_dec_ref(v_a_269_);
v___x_285_ = lean_box(0);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_285_);
v___x_287_ = v___x_279_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_b_270_);
lean_dec_ref(v_a_269_);
v_a_290_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_276_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_276_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_298_, v_b_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* v_00_u03b1_306_, lean_object* v_msg_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* v_00_u03b1_314_, lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(v_00_u03b1_314_, v_msg_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* v_p_322_, lean_object* v___x_323_, lean_object* v___x_324_, lean_object* v_x_325_, size_t v_x_326_, size_t v_x_327_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_cs_328_; size_t v_j_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_cs_328_ = lean_ctor_get(v_x_325_, 0);
v_j_329_ = lean_usize_shift_right(v_x_326_, v_x_327_);
v___x_330_ = lean_usize_to_nat(v_j_329_);
v___x_331_ = lean_array_get_size(v_cs_328_);
v___x_332_ = lean_nat_dec_lt(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec(v___x_330_);
lean_dec(v_p_322_);
return v_x_325_;
}
else
{
lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_350_; 
lean_inc_ref(v_cs_328_);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_x_325_, 0);
lean_dec(v_unused_351_);
v___x_334_ = v_x_325_;
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
else
{
lean_dec(v_x_325_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_350_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v_i_339_; size_t v___x_340_; size_t v_shift_341_; lean_object* v_v_342_; lean_object* v___x_343_; lean_object* v_xs_x27_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_shift_left(v___x_336_, v_x_327_);
v___x_338_ = lean_usize_sub(v___x_337_, v___x_336_);
v_i_339_ = lean_usize_land(v_x_326_, v___x_338_);
v___x_340_ = ((size_t)5ULL);
v_shift_341_ = lean_usize_sub(v_x_327_, v___x_340_);
v_v_342_ = lean_array_fget(v_cs_328_, v___x_330_);
v___x_343_ = lean_box(0);
v_xs_x27_344_ = lean_array_fset(v_cs_328_, v___x_330_, v___x_343_);
v___x_345_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_322_, v___x_323_, v___x_324_, v_v_342_, v_i_339_, v_shift_341_);
v___x_346_ = lean_array_fset(v_xs_x27_344_, v___x_330_, v___x_345_);
lean_dec(v___x_330_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_346_);
v___x_348_ = v___x_334_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_vs_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_vs_352_ = lean_ctor_get(v_x_325_, 0);
v___x_353_ = lean_usize_to_nat(v_x_326_);
v___x_354_ = lean_array_get_size(v_vs_352_);
v___x_355_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v___x_353_);
lean_dec(v_p_322_);
return v_x_325_;
}
else
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_370_; 
lean_inc_ref(v_vs_352_);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_x_325_, 0);
lean_dec(v_unused_371_);
v___x_357_ = v_x_325_;
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_x_325_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint8_t v___x_359_; lean_object* v_v_360_; lean_object* v___x_361_; lean_object* v_xs_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_359_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
v_v_360_ = lean_array_fget(v_vs_352_, v___x_353_);
v___x_361_ = lean_box(0);
v_xs_x27_362_ = lean_array_fset(v_vs_352_, v___x_353_, v___x_361_);
v___x_363_ = lean_box(9);
v___x_364_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_364_, 0, v_p_322_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*2, v___x_359_);
v___x_365_ = l_Lean_PersistentArray_push___redArg(v_v_360_, v___x_364_);
v___x_366_ = lean_array_fset(v_xs_x27_362_, v___x_353_, v___x_365_);
lean_dec(v___x_353_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_366_);
v___x_368_ = v___x_357_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* v_p_372_, lean_object* v___x_373_, lean_object* v___x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
size_t v_x_280__boxed_378_; size_t v_x_281__boxed_379_; lean_object* v_res_380_; 
v_x_280__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_x_281__boxed_379_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_res_380_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_372_, v___x_373_, v___x_374_, v_x_375_, v_x_280__boxed_378_, v_x_281__boxed_379_);
lean_dec(v___x_374_);
lean_dec(v___x_373_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* v_p_381_, lean_object* v___x_382_, lean_object* v___x_383_, lean_object* v_t_384_, lean_object* v_i_385_){
_start:
{
lean_object* v_root_386_; lean_object* v_tail_387_; lean_object* v_size_388_; size_t v_shift_389_; lean_object* v_tailOff_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_417_; 
v_root_386_ = lean_ctor_get(v_t_384_, 0);
v_tail_387_ = lean_ctor_get(v_t_384_, 1);
v_size_388_ = lean_ctor_get(v_t_384_, 2);
v_shift_389_ = lean_ctor_get_usize(v_t_384_, 4);
v_tailOff_390_ = lean_ctor_get(v_t_384_, 3);
v_isSharedCheck_417_ = !lean_is_exclusive(v_t_384_);
if (v_isSharedCheck_417_ == 0)
{
v___x_392_ = v_t_384_;
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_tailOff_390_);
lean_inc(v_size_388_);
lean_inc(v_tail_387_);
lean_inc(v_root_386_);
lean_dec(v_t_384_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_le(v_tailOff_390_, v_i_385_);
if (v___x_394_ == 0)
{
size_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_usize_of_nat(v_i_385_);
v___x_396_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_381_, v___x_382_, v___x_383_, v_root_386_, v___x_395_, v_shift_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_396_);
v___x_398_ = v___x_392_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_tail_387_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_size_388_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_tailOff_390_);
lean_ctor_set_usize(v_reuseFailAlloc_399_, 4, v_shift_389_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = lean_nat_sub(v_i_385_, v_tailOff_390_);
v___x_401_ = lean_array_get_size(v_tail_387_);
v___x_402_ = lean_nat_dec_lt(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; 
lean_dec(v___x_400_);
lean_dec(v_p_381_);
if (v_isShared_393_ == 0)
{
v___x_404_ = v___x_392_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_root_386_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_tail_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_size_388_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_tailOff_390_);
lean_ctor_set_usize(v_reuseFailAlloc_405_, 4, v_shift_389_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
uint8_t v___x_406_; lean_object* v_v_407_; lean_object* v___x_408_; lean_object* v_xs_x27_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_406_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
v_v_407_ = lean_array_fget(v_tail_387_, v___x_400_);
v___x_408_ = lean_box(0);
v_xs_x27_409_ = lean_array_fset(v_tail_387_, v___x_400_, v___x_408_);
v___x_410_ = lean_box(9);
v___x_411_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_411_, 0, v_p_381_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*2, v___x_406_);
v___x_412_ = l_Lean_PersistentArray_push___redArg(v_v_407_, v___x_411_);
v___x_413_ = lean_array_fset(v_xs_x27_409_, v___x_400_, v___x_412_);
lean_dec(v___x_400_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_413_);
v___x_415_ = v___x_392_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_root_386_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_size_388_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_tailOff_390_);
lean_ctor_set_usize(v_reuseFailAlloc_416_, 4, v_shift_389_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* v_p_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_t_421_, lean_object* v_i_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_418_, v___x_419_, v___x_420_, v_t_421_, v_i_422_);
lean_dec(v_i_422_);
lean_dec(v___x_420_);
lean_dec(v___x_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* v_a_424_, lean_object* v_p_425_, lean_object* v_one_426_, lean_object* v_s_427_){
_start:
{
lean_object* v_structs_428_; lean_object* v_typeIdOf_429_; lean_object* v_exprToStructId_430_; lean_object* v_exprToStructIdEntries_431_; lean_object* v_forbiddenNatModules_432_; lean_object* v_natStructs_433_; lean_object* v_natTypeIdOf_434_; lean_object* v_exprToNatStructId_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_structs_428_ = lean_ctor_get(v_s_427_, 0);
v_typeIdOf_429_ = lean_ctor_get(v_s_427_, 1);
v_exprToStructId_430_ = lean_ctor_get(v_s_427_, 2);
v_exprToStructIdEntries_431_ = lean_ctor_get(v_s_427_, 3);
v_forbiddenNatModules_432_ = lean_ctor_get(v_s_427_, 4);
v_natStructs_433_ = lean_ctor_get(v_s_427_, 5);
v_natTypeIdOf_434_ = lean_ctor_get(v_s_427_, 6);
v_exprToNatStructId_435_ = lean_ctor_get(v_s_427_, 7);
v___x_436_ = lean_array_get_size(v_structs_428_);
v___x_437_ = lean_nat_dec_lt(v_a_424_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v_p_425_);
return v_s_427_;
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_499_; 
lean_inc_ref(v_exprToNatStructId_435_);
lean_inc_ref(v_natTypeIdOf_434_);
lean_inc_ref(v_natStructs_433_);
lean_inc_ref(v_forbiddenNatModules_432_);
lean_inc_ref(v_exprToStructIdEntries_431_);
lean_inc_ref(v_exprToStructId_430_);
lean_inc_ref(v_typeIdOf_429_);
lean_inc_ref(v_structs_428_);
v_isSharedCheck_499_ = !lean_is_exclusive(v_s_427_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; lean_object* v_unused_506_; lean_object* v_unused_507_; 
v_unused_500_ = lean_ctor_get(v_s_427_, 7);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_s_427_, 6);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_s_427_, 5);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_s_427_, 4);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_s_427_, 3);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_s_427_, 2);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_s_427_, 1);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_s_427_, 0);
lean_dec(v_unused_507_);
v___x_439_ = v_s_427_;
v_isShared_440_ = v_isSharedCheck_499_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_s_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_499_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_v_441_; lean_object* v_id_442_; lean_object* v_ringId_x3f_443_; lean_object* v_type_444_; lean_object* v_u_445_; lean_object* v_intModuleInst_446_; lean_object* v_leInst_x3f_447_; lean_object* v_ltInst_x3f_448_; lean_object* v_lawfulOrderLTInst_x3f_449_; lean_object* v_isPreorderInst_x3f_450_; lean_object* v_orderedAddInst_x3f_451_; lean_object* v_isLinearInst_x3f_452_; lean_object* v_noNatDivInst_x3f_453_; lean_object* v_ringInst_x3f_454_; lean_object* v_commRingInst_x3f_455_; lean_object* v_orderedRingInst_x3f_456_; lean_object* v_fieldInst_x3f_457_; lean_object* v_charInst_x3f_458_; lean_object* v_zero_459_; lean_object* v_ofNatZero_460_; lean_object* v_one_x3f_461_; lean_object* v_leFn_x3f_462_; lean_object* v_ltFn_x3f_463_; lean_object* v_addFn_464_; lean_object* v_zsmulFn_465_; lean_object* v_nsmulFn_466_; lean_object* v_zsmulFn_x3f_467_; lean_object* v_nsmulFn_x3f_468_; lean_object* v_homomulFn_x3f_469_; lean_object* v_subFn_470_; lean_object* v_negFn_471_; lean_object* v_vars_472_; lean_object* v_varMap_473_; lean_object* v_lowers_474_; lean_object* v_uppers_475_; lean_object* v_diseqs_476_; lean_object* v_assignment_477_; uint8_t v_caseSplits_478_; lean_object* v_conflict_x3f_479_; lean_object* v_diseqSplits_480_; lean_object* v_elimEqs_481_; lean_object* v_elimStack_482_; lean_object* v_occurs_483_; lean_object* v_ignored_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_498_; 
v_v_441_ = lean_array_fget(v_structs_428_, v_a_424_);
v_id_442_ = lean_ctor_get(v_v_441_, 0);
v_ringId_x3f_443_ = lean_ctor_get(v_v_441_, 1);
v_type_444_ = lean_ctor_get(v_v_441_, 2);
v_u_445_ = lean_ctor_get(v_v_441_, 3);
v_intModuleInst_446_ = lean_ctor_get(v_v_441_, 4);
v_leInst_x3f_447_ = lean_ctor_get(v_v_441_, 5);
v_ltInst_x3f_448_ = lean_ctor_get(v_v_441_, 6);
v_lawfulOrderLTInst_x3f_449_ = lean_ctor_get(v_v_441_, 7);
v_isPreorderInst_x3f_450_ = lean_ctor_get(v_v_441_, 8);
v_orderedAddInst_x3f_451_ = lean_ctor_get(v_v_441_, 9);
v_isLinearInst_x3f_452_ = lean_ctor_get(v_v_441_, 10);
v_noNatDivInst_x3f_453_ = lean_ctor_get(v_v_441_, 11);
v_ringInst_x3f_454_ = lean_ctor_get(v_v_441_, 12);
v_commRingInst_x3f_455_ = lean_ctor_get(v_v_441_, 13);
v_orderedRingInst_x3f_456_ = lean_ctor_get(v_v_441_, 14);
v_fieldInst_x3f_457_ = lean_ctor_get(v_v_441_, 15);
v_charInst_x3f_458_ = lean_ctor_get(v_v_441_, 16);
v_zero_459_ = lean_ctor_get(v_v_441_, 17);
v_ofNatZero_460_ = lean_ctor_get(v_v_441_, 18);
v_one_x3f_461_ = lean_ctor_get(v_v_441_, 19);
v_leFn_x3f_462_ = lean_ctor_get(v_v_441_, 20);
v_ltFn_x3f_463_ = lean_ctor_get(v_v_441_, 21);
v_addFn_464_ = lean_ctor_get(v_v_441_, 22);
v_zsmulFn_465_ = lean_ctor_get(v_v_441_, 23);
v_nsmulFn_466_ = lean_ctor_get(v_v_441_, 24);
v_zsmulFn_x3f_467_ = lean_ctor_get(v_v_441_, 25);
v_nsmulFn_x3f_468_ = lean_ctor_get(v_v_441_, 26);
v_homomulFn_x3f_469_ = lean_ctor_get(v_v_441_, 27);
v_subFn_470_ = lean_ctor_get(v_v_441_, 28);
v_negFn_471_ = lean_ctor_get(v_v_441_, 29);
v_vars_472_ = lean_ctor_get(v_v_441_, 30);
v_varMap_473_ = lean_ctor_get(v_v_441_, 31);
v_lowers_474_ = lean_ctor_get(v_v_441_, 32);
v_uppers_475_ = lean_ctor_get(v_v_441_, 33);
v_diseqs_476_ = lean_ctor_get(v_v_441_, 34);
v_assignment_477_ = lean_ctor_get(v_v_441_, 35);
v_caseSplits_478_ = lean_ctor_get_uint8(v_v_441_, sizeof(void*)*42);
v_conflict_x3f_479_ = lean_ctor_get(v_v_441_, 36);
v_diseqSplits_480_ = lean_ctor_get(v_v_441_, 37);
v_elimEqs_481_ = lean_ctor_get(v_v_441_, 38);
v_elimStack_482_ = lean_ctor_get(v_v_441_, 39);
v_occurs_483_ = lean_ctor_get(v_v_441_, 40);
v_ignored_484_ = lean_ctor_get(v_v_441_, 41);
v_isSharedCheck_498_ = !lean_is_exclusive(v_v_441_);
if (v_isSharedCheck_498_ == 0)
{
v___x_486_ = v_v_441_;
v_isShared_487_ = v_isSharedCheck_498_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_ignored_484_);
lean_inc(v_occurs_483_);
lean_inc(v_elimStack_482_);
lean_inc(v_elimEqs_481_);
lean_inc(v_diseqSplits_480_);
lean_inc(v_conflict_x3f_479_);
lean_inc(v_assignment_477_);
lean_inc(v_diseqs_476_);
lean_inc(v_uppers_475_);
lean_inc(v_lowers_474_);
lean_inc(v_varMap_473_);
lean_inc(v_vars_472_);
lean_inc(v_negFn_471_);
lean_inc(v_subFn_470_);
lean_inc(v_homomulFn_x3f_469_);
lean_inc(v_nsmulFn_x3f_468_);
lean_inc(v_zsmulFn_x3f_467_);
lean_inc(v_nsmulFn_466_);
lean_inc(v_zsmulFn_465_);
lean_inc(v_addFn_464_);
lean_inc(v_ltFn_x3f_463_);
lean_inc(v_leFn_x3f_462_);
lean_inc(v_one_x3f_461_);
lean_inc(v_ofNatZero_460_);
lean_inc(v_zero_459_);
lean_inc(v_charInst_x3f_458_);
lean_inc(v_fieldInst_x3f_457_);
lean_inc(v_orderedRingInst_x3f_456_);
lean_inc(v_commRingInst_x3f_455_);
lean_inc(v_ringInst_x3f_454_);
lean_inc(v_noNatDivInst_x3f_453_);
lean_inc(v_isLinearInst_x3f_452_);
lean_inc(v_orderedAddInst_x3f_451_);
lean_inc(v_isPreorderInst_x3f_450_);
lean_inc(v_lawfulOrderLTInst_x3f_449_);
lean_inc(v_ltInst_x3f_448_);
lean_inc(v_leInst_x3f_447_);
lean_inc(v_intModuleInst_446_);
lean_inc(v_u_445_);
lean_inc(v_type_444_);
lean_inc(v_ringId_x3f_443_);
lean_inc(v_id_442_);
lean_dec(v_v_441_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_498_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v_xs_x27_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = lean_box(0);
v_xs_x27_489_ = lean_array_fset(v_structs_428_, v_a_424_, v___x_488_);
v___x_490_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_425_, v_a_424_, v___x_436_, v_lowers_474_, v_one_426_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 32, v___x_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_id_442_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_ringId_x3f_443_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_type_444_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_u_445_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_intModuleInst_446_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_leInst_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_497_, 6, v_ltInst_x3f_448_);
lean_ctor_set(v_reuseFailAlloc_497_, 7, v_lawfulOrderLTInst_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_497_, 8, v_isPreorderInst_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_497_, 9, v_orderedAddInst_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_497_, 10, v_isLinearInst_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_497_, 11, v_noNatDivInst_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_497_, 12, v_ringInst_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_497_, 13, v_commRingInst_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_497_, 14, v_orderedRingInst_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_497_, 15, v_fieldInst_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_497_, 16, v_charInst_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_497_, 17, v_zero_459_);
lean_ctor_set(v_reuseFailAlloc_497_, 18, v_ofNatZero_460_);
lean_ctor_set(v_reuseFailAlloc_497_, 19, v_one_x3f_461_);
lean_ctor_set(v_reuseFailAlloc_497_, 20, v_leFn_x3f_462_);
lean_ctor_set(v_reuseFailAlloc_497_, 21, v_ltFn_x3f_463_);
lean_ctor_set(v_reuseFailAlloc_497_, 22, v_addFn_464_);
lean_ctor_set(v_reuseFailAlloc_497_, 23, v_zsmulFn_465_);
lean_ctor_set(v_reuseFailAlloc_497_, 24, v_nsmulFn_466_);
lean_ctor_set(v_reuseFailAlloc_497_, 25, v_zsmulFn_x3f_467_);
lean_ctor_set(v_reuseFailAlloc_497_, 26, v_nsmulFn_x3f_468_);
lean_ctor_set(v_reuseFailAlloc_497_, 27, v_homomulFn_x3f_469_);
lean_ctor_set(v_reuseFailAlloc_497_, 28, v_subFn_470_);
lean_ctor_set(v_reuseFailAlloc_497_, 29, v_negFn_471_);
lean_ctor_set(v_reuseFailAlloc_497_, 30, v_vars_472_);
lean_ctor_set(v_reuseFailAlloc_497_, 31, v_varMap_473_);
lean_ctor_set(v_reuseFailAlloc_497_, 32, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_497_, 33, v_uppers_475_);
lean_ctor_set(v_reuseFailAlloc_497_, 34, v_diseqs_476_);
lean_ctor_set(v_reuseFailAlloc_497_, 35, v_assignment_477_);
lean_ctor_set(v_reuseFailAlloc_497_, 36, v_conflict_x3f_479_);
lean_ctor_set(v_reuseFailAlloc_497_, 37, v_diseqSplits_480_);
lean_ctor_set(v_reuseFailAlloc_497_, 38, v_elimEqs_481_);
lean_ctor_set(v_reuseFailAlloc_497_, 39, v_elimStack_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 40, v_occurs_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 41, v_ignored_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*42, v_caseSplits_478_);
v___x_492_ = v_reuseFailAlloc_497_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_array_fset(v_xs_x27_489_, v_a_424_, v___x_492_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_493_);
v___x_495_ = v___x_439_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_typeIdOf_429_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_exprToStructId_430_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_exprToStructIdEntries_431_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_forbiddenNatModules_432_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_natStructs_433_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_natTypeIdOf_434_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_exprToNatStructId_435_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* v_a_508_, lean_object* v_p_509_, lean_object* v_one_510_, lean_object* v_s_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(v_a_508_, v_p_509_, v_one_510_, v_s_511_);
lean_dec(v_one_510_);
lean_dec(v_a_508_);
return v_res_512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_to_int(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_516_ = lean_int_neg(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* v_one_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v_p_523_; lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_522_ = lean_box(0);
lean_inc(v_one_517_);
v_p_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_523_, 0, v___x_521_);
lean_ctor_set(v_p_523_, 1, v_one_517_);
lean_ctor_set(v_p_523_, 2, v___x_522_);
lean_inc(v_a_518_);
v___f_524_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_524_, 0, v_a_518_);
lean_closure_set(v___f_524_, 1, v_p_523_);
lean_closure_set(v___f_524_, 2, v_one_517_);
v___x_525_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_526_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_525_, v___f_524_, v_a_519_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* v_one_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* v_one_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_532_, v_a_533_, v_a_534_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* v_one_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
lean_dec(v_a_547_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* v_p_560_, lean_object* v_x_561_, size_t v_x_562_, size_t v_x_563_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_cs_564_; size_t v_j_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_cs_564_ = lean_ctor_get(v_x_561_, 0);
v_j_565_ = lean_usize_shift_right(v_x_562_, v_x_563_);
v___x_566_ = lean_usize_to_nat(v_j_565_);
v___x_567_ = lean_array_get_size(v_cs_564_);
v___x_568_ = lean_nat_dec_lt(v___x_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v___x_566_);
lean_dec(v_p_560_);
return v_x_561_;
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
lean_inc_ref(v_cs_564_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_x_561_, 0);
lean_dec(v_unused_587_);
v___x_570_ = v_x_561_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_x_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v_i_575_; size_t v___x_576_; size_t v_shift_577_; lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_xs_x27_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_shift_left(v___x_572_, v_x_563_);
v___x_574_ = lean_usize_sub(v___x_573_, v___x_572_);
v_i_575_ = lean_usize_land(v_x_562_, v___x_574_);
v___x_576_ = ((size_t)5ULL);
v_shift_577_ = lean_usize_sub(v_x_563_, v___x_576_);
v_v_578_ = lean_array_fget(v_cs_564_, v___x_566_);
v___x_579_ = lean_box(0);
v_xs_x27_580_ = lean_array_fset(v_cs_564_, v___x_566_, v___x_579_);
v___x_581_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_560_, v_v_578_, v_i_575_, v_shift_577_);
v___x_582_ = lean_array_fset(v_xs_x27_580_, v___x_566_, v___x_581_);
lean_dec(v___x_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_582_);
v___x_584_ = v___x_570_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_vs_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_vs_588_ = lean_ctor_get(v_x_561_, 0);
v___x_589_ = lean_usize_to_nat(v_x_562_);
v___x_590_ = lean_array_get_size(v_vs_588_);
v___x_591_ = lean_nat_dec_lt(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v___x_589_);
lean_dec(v_p_560_);
return v_x_561_;
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_605_; 
lean_inc_ref(v_vs_588_);
v_isSharedCheck_605_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v_x_561_, 0);
lean_dec(v_unused_606_);
v___x_593_ = v_x_561_;
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_x_561_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_v_595_; lean_object* v___x_596_; lean_object* v_xs_x27_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_v_595_ = lean_array_fget(v_vs_588_, v___x_589_);
v___x_596_ = lean_box(0);
v_xs_x27_597_ = lean_array_fset(v_vs_588_, v___x_589_, v___x_596_);
v___x_598_ = lean_box(6);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_p_560_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Lean_PersistentArray_push___redArg(v_v_595_, v___x_599_);
v___x_601_ = lean_array_fset(v_xs_x27_597_, v___x_589_, v___x_600_);
lean_dec(v___x_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_601_);
v___x_603_ = v___x_593_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* v_p_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v_x_263__boxed_611_; size_t v_x_264__boxed_612_; lean_object* v_res_613_; 
v_x_263__boxed_611_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_x_264__boxed_612_ = lean_unbox_usize(v_x_610_);
lean_dec(v_x_610_);
v_res_613_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_607_, v_x_608_, v_x_263__boxed_611_, v_x_264__boxed_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* v_p_614_, lean_object* v_t_615_, lean_object* v_i_616_){
_start:
{
lean_object* v_root_617_; lean_object* v_tail_618_; lean_object* v_size_619_; size_t v_shift_620_; lean_object* v_tailOff_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_647_; 
v_root_617_ = lean_ctor_get(v_t_615_, 0);
v_tail_618_ = lean_ctor_get(v_t_615_, 1);
v_size_619_ = lean_ctor_get(v_t_615_, 2);
v_shift_620_ = lean_ctor_get_usize(v_t_615_, 4);
v_tailOff_621_ = lean_ctor_get(v_t_615_, 3);
v_isSharedCheck_647_ = !lean_is_exclusive(v_t_615_);
if (v_isSharedCheck_647_ == 0)
{
v___x_623_ = v_t_615_;
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tailOff_621_);
lean_inc(v_size_619_);
lean_inc(v_tail_618_);
lean_inc(v_root_617_);
lean_dec(v_t_615_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___x_625_; 
v___x_625_ = lean_nat_dec_le(v_tailOff_621_, v_i_616_);
if (v___x_625_ == 0)
{
size_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_usize_of_nat(v_i_616_);
v___x_627_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_614_, v_root_617_, v___x_626_, v_shift_620_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_627_);
v___x_629_ = v___x_623_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_tail_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_size_619_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_tailOff_621_);
lean_ctor_set_usize(v_reuseFailAlloc_630_, 4, v_shift_620_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_nat_sub(v_i_616_, v_tailOff_621_);
v___x_632_ = lean_array_get_size(v_tail_618_);
v___x_633_ = lean_nat_dec_lt(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v___x_631_);
lean_dec(v_p_614_);
if (v_isShared_624_ == 0)
{
v___x_635_ = v___x_623_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_root_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_tail_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_size_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_tailOff_621_);
lean_ctor_set_usize(v_reuseFailAlloc_636_, 4, v_shift_620_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
else
{
lean_object* v_v_637_; lean_object* v___x_638_; lean_object* v_xs_x27_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v_v_637_ = lean_array_fget(v_tail_618_, v___x_631_);
v___x_638_ = lean_box(0);
v_xs_x27_639_ = lean_array_fset(v_tail_618_, v___x_631_, v___x_638_);
v___x_640_ = lean_box(6);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_p_614_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_PersistentArray_push___redArg(v_v_637_, v___x_641_);
v___x_643_ = lean_array_fset(v_xs_x27_639_, v___x_631_, v___x_642_);
lean_dec(v___x_631_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_643_);
v___x_645_ = v___x_623_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_root_617_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_size_619_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_tailOff_621_);
lean_ctor_set_usize(v_reuseFailAlloc_646_, 4, v_shift_620_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* v_p_648_, lean_object* v_t_649_, lean_object* v_i_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_648_, v_t_649_, v_i_650_);
lean_dec(v_i_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* v_a_652_, lean_object* v_p_653_, lean_object* v_one_654_, lean_object* v_s_655_){
_start:
{
lean_object* v_structs_656_; lean_object* v_typeIdOf_657_; lean_object* v_exprToStructId_658_; lean_object* v_exprToStructIdEntries_659_; lean_object* v_forbiddenNatModules_660_; lean_object* v_natStructs_661_; lean_object* v_natTypeIdOf_662_; lean_object* v_exprToNatStructId_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_structs_656_ = lean_ctor_get(v_s_655_, 0);
v_typeIdOf_657_ = lean_ctor_get(v_s_655_, 1);
v_exprToStructId_658_ = lean_ctor_get(v_s_655_, 2);
v_exprToStructIdEntries_659_ = lean_ctor_get(v_s_655_, 3);
v_forbiddenNatModules_660_ = lean_ctor_get(v_s_655_, 4);
v_natStructs_661_ = lean_ctor_get(v_s_655_, 5);
v_natTypeIdOf_662_ = lean_ctor_get(v_s_655_, 6);
v_exprToNatStructId_663_ = lean_ctor_get(v_s_655_, 7);
v___x_664_ = lean_array_get_size(v_structs_656_);
v___x_665_ = lean_nat_dec_lt(v_a_652_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_p_653_);
return v_s_655_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_727_; 
lean_inc_ref(v_exprToNatStructId_663_);
lean_inc_ref(v_natTypeIdOf_662_);
lean_inc_ref(v_natStructs_661_);
lean_inc_ref(v_forbiddenNatModules_660_);
lean_inc_ref(v_exprToStructIdEntries_659_);
lean_inc_ref(v_exprToStructId_658_);
lean_inc_ref(v_typeIdOf_657_);
lean_inc_ref(v_structs_656_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_s_655_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; 
v_unused_728_ = lean_ctor_get(v_s_655_, 7);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_s_655_, 6);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_s_655_, 5);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_s_655_, 4);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_s_655_, 3);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_s_655_, 2);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_s_655_, 1);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_s_655_, 0);
lean_dec(v_unused_735_);
v___x_667_ = v_s_655_;
v_isShared_668_ = v_isSharedCheck_727_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_s_655_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_727_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_v_669_; lean_object* v_id_670_; lean_object* v_ringId_x3f_671_; lean_object* v_type_672_; lean_object* v_u_673_; lean_object* v_intModuleInst_674_; lean_object* v_leInst_x3f_675_; lean_object* v_ltInst_x3f_676_; lean_object* v_lawfulOrderLTInst_x3f_677_; lean_object* v_isPreorderInst_x3f_678_; lean_object* v_orderedAddInst_x3f_679_; lean_object* v_isLinearInst_x3f_680_; lean_object* v_noNatDivInst_x3f_681_; lean_object* v_ringInst_x3f_682_; lean_object* v_commRingInst_x3f_683_; lean_object* v_orderedRingInst_x3f_684_; lean_object* v_fieldInst_x3f_685_; lean_object* v_charInst_x3f_686_; lean_object* v_zero_687_; lean_object* v_ofNatZero_688_; lean_object* v_one_x3f_689_; lean_object* v_leFn_x3f_690_; lean_object* v_ltFn_x3f_691_; lean_object* v_addFn_692_; lean_object* v_zsmulFn_693_; lean_object* v_nsmulFn_694_; lean_object* v_zsmulFn_x3f_695_; lean_object* v_nsmulFn_x3f_696_; lean_object* v_homomulFn_x3f_697_; lean_object* v_subFn_698_; lean_object* v_negFn_699_; lean_object* v_vars_700_; lean_object* v_varMap_701_; lean_object* v_lowers_702_; lean_object* v_uppers_703_; lean_object* v_diseqs_704_; lean_object* v_assignment_705_; uint8_t v_caseSplits_706_; lean_object* v_conflict_x3f_707_; lean_object* v_diseqSplits_708_; lean_object* v_elimEqs_709_; lean_object* v_elimStack_710_; lean_object* v_occurs_711_; lean_object* v_ignored_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_726_; 
v_v_669_ = lean_array_fget(v_structs_656_, v_a_652_);
v_id_670_ = lean_ctor_get(v_v_669_, 0);
v_ringId_x3f_671_ = lean_ctor_get(v_v_669_, 1);
v_type_672_ = lean_ctor_get(v_v_669_, 2);
v_u_673_ = lean_ctor_get(v_v_669_, 3);
v_intModuleInst_674_ = lean_ctor_get(v_v_669_, 4);
v_leInst_x3f_675_ = lean_ctor_get(v_v_669_, 5);
v_ltInst_x3f_676_ = lean_ctor_get(v_v_669_, 6);
v_lawfulOrderLTInst_x3f_677_ = lean_ctor_get(v_v_669_, 7);
v_isPreorderInst_x3f_678_ = lean_ctor_get(v_v_669_, 8);
v_orderedAddInst_x3f_679_ = lean_ctor_get(v_v_669_, 9);
v_isLinearInst_x3f_680_ = lean_ctor_get(v_v_669_, 10);
v_noNatDivInst_x3f_681_ = lean_ctor_get(v_v_669_, 11);
v_ringInst_x3f_682_ = lean_ctor_get(v_v_669_, 12);
v_commRingInst_x3f_683_ = lean_ctor_get(v_v_669_, 13);
v_orderedRingInst_x3f_684_ = lean_ctor_get(v_v_669_, 14);
v_fieldInst_x3f_685_ = lean_ctor_get(v_v_669_, 15);
v_charInst_x3f_686_ = lean_ctor_get(v_v_669_, 16);
v_zero_687_ = lean_ctor_get(v_v_669_, 17);
v_ofNatZero_688_ = lean_ctor_get(v_v_669_, 18);
v_one_x3f_689_ = lean_ctor_get(v_v_669_, 19);
v_leFn_x3f_690_ = lean_ctor_get(v_v_669_, 20);
v_ltFn_x3f_691_ = lean_ctor_get(v_v_669_, 21);
v_addFn_692_ = lean_ctor_get(v_v_669_, 22);
v_zsmulFn_693_ = lean_ctor_get(v_v_669_, 23);
v_nsmulFn_694_ = lean_ctor_get(v_v_669_, 24);
v_zsmulFn_x3f_695_ = lean_ctor_get(v_v_669_, 25);
v_nsmulFn_x3f_696_ = lean_ctor_get(v_v_669_, 26);
v_homomulFn_x3f_697_ = lean_ctor_get(v_v_669_, 27);
v_subFn_698_ = lean_ctor_get(v_v_669_, 28);
v_negFn_699_ = lean_ctor_get(v_v_669_, 29);
v_vars_700_ = lean_ctor_get(v_v_669_, 30);
v_varMap_701_ = lean_ctor_get(v_v_669_, 31);
v_lowers_702_ = lean_ctor_get(v_v_669_, 32);
v_uppers_703_ = lean_ctor_get(v_v_669_, 33);
v_diseqs_704_ = lean_ctor_get(v_v_669_, 34);
v_assignment_705_ = lean_ctor_get(v_v_669_, 35);
v_caseSplits_706_ = lean_ctor_get_uint8(v_v_669_, sizeof(void*)*42);
v_conflict_x3f_707_ = lean_ctor_get(v_v_669_, 36);
v_diseqSplits_708_ = lean_ctor_get(v_v_669_, 37);
v_elimEqs_709_ = lean_ctor_get(v_v_669_, 38);
v_elimStack_710_ = lean_ctor_get(v_v_669_, 39);
v_occurs_711_ = lean_ctor_get(v_v_669_, 40);
v_ignored_712_ = lean_ctor_get(v_v_669_, 41);
v_isSharedCheck_726_ = !lean_is_exclusive(v_v_669_);
if (v_isSharedCheck_726_ == 0)
{
v___x_714_ = v_v_669_;
v_isShared_715_ = v_isSharedCheck_726_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_ignored_712_);
lean_inc(v_occurs_711_);
lean_inc(v_elimStack_710_);
lean_inc(v_elimEqs_709_);
lean_inc(v_diseqSplits_708_);
lean_inc(v_conflict_x3f_707_);
lean_inc(v_assignment_705_);
lean_inc(v_diseqs_704_);
lean_inc(v_uppers_703_);
lean_inc(v_lowers_702_);
lean_inc(v_varMap_701_);
lean_inc(v_vars_700_);
lean_inc(v_negFn_699_);
lean_inc(v_subFn_698_);
lean_inc(v_homomulFn_x3f_697_);
lean_inc(v_nsmulFn_x3f_696_);
lean_inc(v_zsmulFn_x3f_695_);
lean_inc(v_nsmulFn_694_);
lean_inc(v_zsmulFn_693_);
lean_inc(v_addFn_692_);
lean_inc(v_ltFn_x3f_691_);
lean_inc(v_leFn_x3f_690_);
lean_inc(v_one_x3f_689_);
lean_inc(v_ofNatZero_688_);
lean_inc(v_zero_687_);
lean_inc(v_charInst_x3f_686_);
lean_inc(v_fieldInst_x3f_685_);
lean_inc(v_orderedRingInst_x3f_684_);
lean_inc(v_commRingInst_x3f_683_);
lean_inc(v_ringInst_x3f_682_);
lean_inc(v_noNatDivInst_x3f_681_);
lean_inc(v_isLinearInst_x3f_680_);
lean_inc(v_orderedAddInst_x3f_679_);
lean_inc(v_isPreorderInst_x3f_678_);
lean_inc(v_lawfulOrderLTInst_x3f_677_);
lean_inc(v_ltInst_x3f_676_);
lean_inc(v_leInst_x3f_675_);
lean_inc(v_intModuleInst_674_);
lean_inc(v_u_673_);
lean_inc(v_type_672_);
lean_inc(v_ringId_x3f_671_);
lean_inc(v_id_670_);
lean_dec(v_v_669_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_726_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v_xs_x27_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_716_ = lean_box(0);
v_xs_x27_717_ = lean_array_fset(v_structs_656_, v_a_652_, v___x_716_);
v___x_718_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_653_, v_diseqs_704_, v_one_654_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 34, v___x_718_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_id_670_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_ringId_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_type_672_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_u_673_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_intModuleInst_674_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_leInst_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_ltInst_x3f_676_);
lean_ctor_set(v_reuseFailAlloc_725_, 7, v_lawfulOrderLTInst_x3f_677_);
lean_ctor_set(v_reuseFailAlloc_725_, 8, v_isPreorderInst_x3f_678_);
lean_ctor_set(v_reuseFailAlloc_725_, 9, v_orderedAddInst_x3f_679_);
lean_ctor_set(v_reuseFailAlloc_725_, 10, v_isLinearInst_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_725_, 11, v_noNatDivInst_x3f_681_);
lean_ctor_set(v_reuseFailAlloc_725_, 12, v_ringInst_x3f_682_);
lean_ctor_set(v_reuseFailAlloc_725_, 13, v_commRingInst_x3f_683_);
lean_ctor_set(v_reuseFailAlloc_725_, 14, v_orderedRingInst_x3f_684_);
lean_ctor_set(v_reuseFailAlloc_725_, 15, v_fieldInst_x3f_685_);
lean_ctor_set(v_reuseFailAlloc_725_, 16, v_charInst_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_725_, 17, v_zero_687_);
lean_ctor_set(v_reuseFailAlloc_725_, 18, v_ofNatZero_688_);
lean_ctor_set(v_reuseFailAlloc_725_, 19, v_one_x3f_689_);
lean_ctor_set(v_reuseFailAlloc_725_, 20, v_leFn_x3f_690_);
lean_ctor_set(v_reuseFailAlloc_725_, 21, v_ltFn_x3f_691_);
lean_ctor_set(v_reuseFailAlloc_725_, 22, v_addFn_692_);
lean_ctor_set(v_reuseFailAlloc_725_, 23, v_zsmulFn_693_);
lean_ctor_set(v_reuseFailAlloc_725_, 24, v_nsmulFn_694_);
lean_ctor_set(v_reuseFailAlloc_725_, 25, v_zsmulFn_x3f_695_);
lean_ctor_set(v_reuseFailAlloc_725_, 26, v_nsmulFn_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_725_, 27, v_homomulFn_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_725_, 28, v_subFn_698_);
lean_ctor_set(v_reuseFailAlloc_725_, 29, v_negFn_699_);
lean_ctor_set(v_reuseFailAlloc_725_, 30, v_vars_700_);
lean_ctor_set(v_reuseFailAlloc_725_, 31, v_varMap_701_);
lean_ctor_set(v_reuseFailAlloc_725_, 32, v_lowers_702_);
lean_ctor_set(v_reuseFailAlloc_725_, 33, v_uppers_703_);
lean_ctor_set(v_reuseFailAlloc_725_, 34, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_725_, 35, v_assignment_705_);
lean_ctor_set(v_reuseFailAlloc_725_, 36, v_conflict_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_725_, 37, v_diseqSplits_708_);
lean_ctor_set(v_reuseFailAlloc_725_, 38, v_elimEqs_709_);
lean_ctor_set(v_reuseFailAlloc_725_, 39, v_elimStack_710_);
lean_ctor_set(v_reuseFailAlloc_725_, 40, v_occurs_711_);
lean_ctor_set(v_reuseFailAlloc_725_, 41, v_ignored_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*42, v_caseSplits_706_);
v___x_720_ = v_reuseFailAlloc_725_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_array_fset(v_xs_x27_717_, v_a_652_, v___x_720_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_721_);
v___x_723_ = v___x_667_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_typeIdOf_657_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_exprToStructId_658_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_exprToStructIdEntries_659_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_forbiddenNatModules_660_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v_natStructs_661_);
lean_ctor_set(v_reuseFailAlloc_724_, 6, v_natTypeIdOf_662_);
lean_ctor_set(v_reuseFailAlloc_724_, 7, v_exprToNatStructId_663_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* v_a_736_, lean_object* v_p_737_, lean_object* v_one_738_, lean_object* v_s_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(v_a_736_, v_p_737_, v_one_738_, v_s_739_);
lean_dec(v_one_738_);
lean_dec(v_a_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* v_one_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_p_747_; lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_746_ = lean_box(0);
lean_inc(v_one_741_);
v_p_747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_747_, 0, v___x_745_);
lean_ctor_set(v_p_747_, 1, v_one_741_);
lean_ctor_set(v_p_747_, 2, v___x_746_);
lean_inc(v_a_742_);
v___f_748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_748_, 0, v_a_742_);
lean_closure_set(v___f_748_, 1, v_p_747_);
lean_closure_set(v___f_748_, 2, v_one_741_);
v___x_749_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_750_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_749_, v___f_748_, v_a_743_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* v_one_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec(v_a_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* v_one_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_756_, v_a_757_, v_a_758_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* v_one_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec(v_a_772_);
lean_dec(v_a_771_);
return v_res_783_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* v_isCharInst_x3f_784_){
_start:
{
if (lean_obj_tag(v_isCharInst_x3f_784_) == 0)
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
else
{
lean_object* v_val_786_; lean_object* v_snd_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_val_786_ = lean_ctor_get(v_isCharInst_x3f_784_, 0);
v_snd_787_ = lean_ctor_get(v_val_786_, 1);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_nat_dec_eq(v_snd_787_, v___x_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; 
v___x_790_ = 1;
return v___x_790_;
}
else
{
uint8_t v___x_791_; 
v___x_791_ = 0;
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_792_);
lean_dec(v_isCharInst_x3f_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(lean_object* v_type_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_796_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v_lia_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v_lia_805_ = lean_ctor_get_uint8(v_a_804_, sizeof(void*)*14 + 23);
lean_dec(v_a_804_);
if (v_lia_805_ == 0)
{
lean_dec_ref(v_type_795_);
goto v___jp_799_;
}
else
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_795_, v_a_797_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
v___x_808_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_808_ == 0)
{
lean_dec_ref_known(v___x_806_, 1);
goto v___jp_799_;
}
else
{
return v___x_806_;
}
}
else
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_type_795_);
v_a_809_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_803_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_803_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
v___jp_799_:
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = 0;
v___x_801_ = lean_box(v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg___boxed(lean_object* v_type_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_822_, v_a_825_, v_a_830_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_848_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_887_; 
v_val_860_ = lean_ctor_get(v_ringId_x3f_848_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_ringId_x3f_848_);
if (v_isSharedCheck_887_ == 0)
{
v___x_862_ = v_ringId_x3f_848_;
v_isShared_863_ = v_isSharedCheck_887_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_val_860_);
lean_dec(v_ringId_x3f_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_887_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = 0;
v___x_865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_865_, 0, v_val_860_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*1, v___x_864_);
v___x_866_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_865_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec_ref_known(v___x_865_, 1);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_878_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_commRingInst_871_; lean_object* v___x_873_; 
v_commRingInst_871_ = lean_ctor_get(v_a_867_, 4);
lean_inc_ref(v_commRingInst_871_);
lean_dec(v_a_867_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_commRingInst_871_);
v___x_873_ = v___x_862_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_commRingInst_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_del_object(v___x_862_);
v_a_879_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_866_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_866_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_ringId_x3f_848_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec(v_a_891_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_917_, lean_object* v_type_918_, lean_object* v_commRingInst_x3f_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_919_) == 1)
{
lean_object* v_val_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_939_; 
v_val_926_ = lean_ctor_get(v_commRingInst_x3f_919_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v_commRingInst_x3f_919_);
if (v_isSharedCheck_939_ == 0)
{
v___x_928_ = v_commRingInst_x3f_919_;
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_val_926_);
lean_dec(v_commRingInst_x3f_919_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_939_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_932_, 0, v_u_917_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_mkConst(v___x_930_, v___x_932_);
v___x_934_ = l_Lean_mkAppB(v___x_933_, v_type_918_, v_val_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_936_ = v___x_928_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_commRingInst_x3f_919_);
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v_u_917_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_mkConst(v___x_940_, v___x_942_);
v___x_944_ = l_Lean_Expr_app___override(v___x_943_, v_type_918_);
v___x_945_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_944_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_946_, lean_object* v_type_947_, lean_object* v_commRingInst_x3f_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_946_, v_type_947_, v_commRingInst_x3f_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_956_, lean_object* v_type_957_, lean_object* v_commRingInst_x3f_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_956_, v_type_957_, v_commRingInst_x3f_958_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_971_, lean_object* v_type_972_, lean_object* v_commRingInst_x3f_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_971_, v_type_972_, v_commRingInst_x3f_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_997_, lean_object* v_type_998_, lean_object* v_ringInst_x3f_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_999_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1019_; 
v_val_1006_ = lean_ctor_get(v_ringInst_x3f_999_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_ringInst_x3f_999_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1008_ = v_ringInst_x3f_999_;
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_val_1006_);
lean_dec(v_ringInst_x3f_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1019_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_u_997_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_mkConst(v___x_1010_, v___x_1012_);
v___x_1014_ = l_Lean_mkAppB(v___x_1013_, v_type_998_, v_val_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1014_);
v___x_1016_ = v___x_1008_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_ringInst_x3f_999_);
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_u_997_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_mkConst(v___x_1020_, v___x_1022_);
v___x_1024_ = l_Lean_Expr_app___override(v___x_1023_, v_type_998_);
v___x_1025_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1024_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1026_, lean_object* v_type_1027_, lean_object* v_ringInst_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1026_, v_type_1027_, v_ringInst_x3f_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1036_, lean_object* v_type_1037_, lean_object* v_ringInst_x3f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1036_, v_type_1037_, v_ringInst_x3f_1038_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1051_, lean_object* v_type_1052_, lean_object* v_ringInst_x3f_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1051_, v_type_1052_, v_ringInst_x3f_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec(v_a_1054_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1077_, lean_object* v_type_1078_, lean_object* v_ringInst_x3f_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1079_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v_val_1086_ = lean_ctor_get(v_ringInst_x3f_1079_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_ringInst_x3f_1079_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1088_ = v_ringInst_x3f_1079_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_val_1086_);
lean_dec(v_ringInst_x3f_1079_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_u_1077_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_mkConst(v___x_1090_, v___x_1092_);
v___x_1094_ = l_Lean_mkAppB(v___x_1093_, v_type_1078_, v_val_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1094_);
v___x_1096_ = v___x_1088_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v_ringInst_x3f_1079_);
v___x_1100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_u_1077_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_mkConst(v___x_1100_, v___x_1102_);
v___x_1104_ = l_Lean_Expr_app___override(v___x_1103_, v_type_1078_);
v___x_1105_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1104_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1106_, lean_object* v_type_1107_, lean_object* v_ringInst_x3f_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1106_, v_type_1107_, v_ringInst_x3f_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1116_, lean_object* v_type_1117_, lean_object* v_ringInst_x3f_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1116_, v_type_1117_, v_ringInst_x3f_1118_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1131_, lean_object* v_type_1132_, lean_object* v_ringInst_x3f_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1131_, v_type_1132_, v_ringInst_x3f_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec(v_a_1134_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1153_, lean_object* v_type_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_u_1153_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
lean_inc_ref(v___x_1168_);
v___x_1169_ = l_Lean_mkConst(v___x_1166_, v___x_1168_);
lean_inc_ref(v_type_1154_);
v___x_1170_ = l_Lean_Expr_app___override(v___x_1169_, v_type_1154_);
v___x_1171_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1170_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1253_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1253_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1253_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
if (lean_obj_tag(v_a_1172_) == 1)
{
lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1174_);
v_val_1176_ = lean_ctor_get(v_a_1172_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_a_1172_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1178_ = v_a_1172_;
v_isShared_1179_ = v_isSharedCheck_1248_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_dec(v_a_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1248_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1181_ = l_Lean_mkConst(v___x_1180_, v___x_1168_);
lean_inc_ref(v_type_1154_);
v___x_1182_ = l_Lean_mkAppB(v___x_1181_, v_type_1154_, v_val_1176_);
v___x_1183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1182_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1239_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1239_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1239_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = l_Lean_Meta_mkNumeral(v_type_1154_, v___x_1195_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_n(v_a_1197_, 2);
lean_dec_ref_known(v___x_1196_, 1);
lean_inc(v_a_1184_);
v___x_1198_ = l_Lean_Meta_isDefEqD(v_a_1184_, v_a_1197_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1203_; 
lean_inc(v_a_1184_);
v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1184_, v_a_1197_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1159_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; uint8_t v_verbose_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v_verbose_1205_ = lean_ctor_get_uint8(v_a_1204_, 0);
lean_dec(v_a_1204_);
if (v_verbose_1205_ == 0)
{
lean_dec(v_a_1202_);
goto v___jp_1188_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Sym_reportIssue(v_a_1202_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_dec_ref_known(v___x_1206_, 1);
goto v___jp_1188_;
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1186_);
lean_dec(v_a_1184_);
lean_del_object(v___x_1178_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
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
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1202_);
lean_del_object(v___x_1186_);
lean_dec(v_a_1184_);
lean_del_object(v___x_1178_);
v_a_1215_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1203_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1203_);
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
else
{
lean_dec(v_a_1197_);
goto v___jp_1188_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1197_);
lean_del_object(v___x_1186_);
lean_dec(v_a_1184_);
lean_del_object(v___x_1178_);
v_a_1223_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1198_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1198_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_del_object(v___x_1186_);
lean_dec(v_a_1184_);
lean_del_object(v___x_1178_);
v_a_1231_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1196_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1196_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
v___jp_1188_:
{
lean_object* v___x_1190_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_a_1184_);
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1184_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1190_);
v___x_1192_ = v___x_1186_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_del_object(v___x_1178_);
lean_dec_ref(v_type_1154_);
v_a_1240_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1183_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1183_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec(v_a_1172_);
lean_dec_ref_known(v___x_1168_, 2);
lean_dec_ref(v_type_1154_);
v___x_1249_ = lean_box(0);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1249_);
v___x_1251_ = v___x_1174_;
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
}
}
else
{
lean_dec_ref_known(v___x_1168_, 2);
lean_dec_ref(v_type_1154_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1254_, lean_object* v_type_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1254_, v_type_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
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
return v_res_1267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1276_, lean_object* v_type_1277_, lean_object* v_semiringInst_x3f_1278_, lean_object* v_leInst_x3f_1279_, lean_object* v_ltInst_x3f_1280_, lean_object* v_preorderInst_x3f_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1278_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1279_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1280_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1281_) == 1)
{
lean_object* v_val_1292_; lean_object* v_val_1293_; lean_object* v_val_1294_; lean_object* v_val_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_isOrdType_1300_; lean_object* v___x_1301_; 
v_val_1292_ = lean_ctor_get(v_semiringInst_x3f_1278_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v_semiringInst_x3f_1278_, 1);
v_val_1293_ = lean_ctor_get(v_leInst_x3f_1279_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v_leInst_x3f_1279_, 1);
v_val_1294_ = lean_ctor_get(v_ltInst_x3f_1280_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v_ltInst_x3f_1280_, 1);
v_val_1295_ = lean_ctor_get(v_preorderInst_x3f_1281_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v_preorderInst_x3f_1281_, 1);
v___x_1296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_u_1276_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_mkConst(v___x_1296_, v___x_1298_);
v_isOrdType_1300_ = l_Lean_mkApp5(v___x_1299_, v_type_1277_, v_val_1292_, v_val_1293_, v_val_1294_, v_val_1295_);
lean_inc_ref(v_isOrdType_1300_);
v___x_1301_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1300_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
if (lean_obj_tag(v_a_1302_) == 1)
{
lean_dec_ref_known(v_a_1302_, 1);
lean_dec_ref(v_isOrdType_1300_);
return v___x_1301_;
}
else
{
lean_object* v___x_1303_; 
lean_dec_ref_known(v___x_1301_, 1);
lean_dec(v_a_1302_);
v___x_1303_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1282_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; uint8_t v_verbose_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v_verbose_1305_ = lean_ctor_get_uint8(v_a_1304_, 0);
lean_dec(v_a_1304_);
if (v_verbose_1305_ == 0)
{
lean_dec_ref(v_isOrdType_1300_);
goto v___jp_1289_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1307_ = l_Lean_indentExpr(v_isOrdType_1300_);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_Meta_Sym_reportIssue(v___x_1308_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_dec_ref_known(v___x_1309_, 1);
goto v___jp_1289_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v_isOrdType_1300_);
v_a_1318_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1303_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1303_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1300_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref_known(v_leInst_x3f_1279_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1278_, 1);
lean_dec(v_preorderInst_x3f_1281_);
lean_dec_ref(v_type_1277_);
lean_dec(v_u_1276_);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_ltInst_x3f_1280_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_ltInst_x3f_1280_, 0);
lean_dec(v_unused_1334_);
v___x_1327_ = v_ltInst_x3f_1280_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_ltInst_x3f_1280_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1329_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref_known(v_semiringInst_x3f_1278_, 1);
lean_dec(v_preorderInst_x3f_1281_);
lean_dec(v_ltInst_x3f_1280_);
lean_dec_ref(v_type_1277_);
lean_dec(v_u_1276_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_leInst_x3f_1279_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_leInst_x3f_1279_, 0);
lean_dec(v_unused_1343_);
v___x_1336_ = v_leInst_x3f_1279_;
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v_leInst_x3f_1279_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_preorderInst_x3f_1281_);
lean_dec(v_ltInst_x3f_1280_);
lean_dec(v_leInst_x3f_1279_);
lean_dec_ref(v_type_1277_);
lean_dec(v_u_1276_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_semiringInst_x3f_1278_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v_semiringInst_x3f_1278_, 0);
lean_dec(v_unused_1352_);
v___x_1345_ = v_semiringInst_x3f_1278_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v_semiringInst_x3f_1278_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v_preorderInst_x3f_1281_);
lean_dec(v_ltInst_x3f_1280_);
lean_dec(v_leInst_x3f_1279_);
lean_dec(v_semiringInst_x3f_1278_);
lean_dec_ref(v_type_1277_);
lean_dec(v_u_1276_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1355_, lean_object* v_type_1356_, lean_object* v_semiringInst_x3f_1357_, lean_object* v_leInst_x3f_1358_, lean_object* v_ltInst_x3f_1359_, lean_object* v_preorderInst_x3f_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1355_, v_type_1356_, v_semiringInst_x3f_1357_, v_leInst_x3f_1358_, v_ltInst_x3f_1359_, v_preorderInst_x3f_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1369_, lean_object* v_type_1370_, lean_object* v_semiringInst_x3f_1371_, lean_object* v_leInst_x3f_1372_, lean_object* v_ltInst_x3f_1373_, lean_object* v_preorderInst_x3f_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1369_, v_type_1370_, v_semiringInst_x3f_1371_, v_leInst_x3f_1372_, v_ltInst_x3f_1373_, v_preorderInst_x3f_1374_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1387_ = _args[0];
lean_object* v_type_1388_ = _args[1];
lean_object* v_semiringInst_x3f_1389_ = _args[2];
lean_object* v_leInst_x3f_1390_ = _args[3];
lean_object* v_ltInst_x3f_1391_ = _args[4];
lean_object* v_preorderInst_x3f_1392_ = _args[5];
lean_object* v_a_1393_ = _args[6];
lean_object* v_a_1394_ = _args[7];
lean_object* v_a_1395_ = _args[8];
lean_object* v_a_1396_ = _args[9];
lean_object* v_a_1397_ = _args[10];
lean_object* v_a_1398_ = _args[11];
lean_object* v_a_1399_ = _args[12];
lean_object* v_a_1400_ = _args[13];
lean_object* v_a_1401_ = _args[14];
lean_object* v_a_1402_ = _args[15];
lean_object* v_a_1403_ = _args[16];
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1387_, v_type_1388_, v_semiringInst_x3f_1389_, v_leInst_x3f_1390_, v_ltInst_x3f_1391_, v_preorderInst_x3f_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec(v_a_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1415_, lean_object* v_type_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_natModuleType_1427_; lean_object* v___x_1428_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_u_1415_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_inc_ref(v___x_1425_);
v___x_1426_ = l_Lean_mkConst(v___x_1423_, v___x_1425_);
lean_inc_ref(v_type_1416_);
v_natModuleType_1427_ = l_Lean_Expr_app___override(v___x_1426_, v_type_1416_);
v___x_1428_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1427_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1442_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
if (lean_obj_tag(v_a_1429_) == 1)
{
lean_object* v_val_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_del_object(v___x_1431_);
v_val_1433_ = lean_ctor_get(v_a_1429_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v_a_1429_, 1);
v___x_1434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1435_ = l_Lean_mkConst(v___x_1434_, v___x_1425_);
v___x_1436_ = l_Lean_mkAppB(v___x_1435_, v_type_1416_, v_val_1433_);
v___x_1437_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1436_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_a_1429_);
lean_dec_ref_known(v___x_1425_, 2);
lean_dec_ref(v_type_1416_);
v___x_1438_ = lean_box(0);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1438_);
v___x_1440_ = v___x_1431_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1425_, 2);
lean_dec_ref(v_type_1416_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1443_, lean_object* v_type_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1443_, v_type_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1452_, lean_object* v_type_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1452_, v_type_1453_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1466_, lean_object* v_type_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1466_, v_type_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec(v_a_1468_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1480_, lean_object* v_u_1481_, lean_object* v_type_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_u_1481_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_mkConst(v_declName_1480_, v___x_1490_);
v___x_1492_ = l_Lean_Expr_app___override(v___x_1491_, v_type_1482_);
v___x_1493_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1492_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1494_, lean_object* v_u_1495_, lean_object* v_type_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1494_, v_u_1495_, v_type_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1504_, lean_object* v_u_1505_, lean_object* v_type_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1504_, v_u_1505_, v_type_1506_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1519_, lean_object* v_u_1520_, lean_object* v_type_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1519_, v_u_1520_, v_type_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec(v_a_1522_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1534_, lean_object* v_u_1535_, lean_object* v_type_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_u_1535_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_mkConst(v_declName_1534_, v___x_1545_);
v___x_1547_ = l_Lean_Expr_app___override(v___x_1546_, v_type_1536_);
v___x_1548_ = l_Lean_Meta_Sym_synthInstance(v___x_1547_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1549_, lean_object* v_u_1550_, lean_object* v_type_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1549_, v_u_1550_, v_type_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1560_, lean_object* v_u_1561_, lean_object* v_type_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1560_, v_u_1561_, v_type_1562_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1575_, lean_object* v_u_1576_, lean_object* v_type_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1575_, v_u_1576_, v_type_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec(v_a_1578_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1590_, lean_object* v_u_1591_, lean_object* v_type_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1600_ = lean_box(0);
lean_inc_n(v_u_1591_, 2);
v___x_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_u_1591_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_u_1591_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_u_1591_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_mkConst(v_declName_1590_, v___x_1603_);
lean_inc_ref_n(v_type_1592_, 2);
v___x_1605_ = l_Lean_mkApp3(v___x_1604_, v_type_1592_, v_type_1592_, v_type_1592_);
v___x_1606_ = l_Lean_Meta_Sym_synthInstance(v___x_1605_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1607_, lean_object* v_u_1608_, lean_object* v_type_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1607_, v_u_1608_, v_type_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1618_, lean_object* v_u_1619_, lean_object* v_type_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1618_, v_u_1619_, v_type_1620_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1633_, lean_object* v_u_1634_, lean_object* v_type_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1633_, v_u_1634_, v_type_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec(v_a_1636_);
return v_res_1647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = l_Lean_Level_ofNat(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1653_, lean_object* v_type_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1664_ = lean_box(0);
lean_inc(v_u_1653_);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_u_1653_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_u_1653_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1663_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = l_Lean_mkConst(v___x_1662_, v___x_1667_);
v___x_1669_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1654_);
v___x_1670_ = l_Lean_mkApp3(v___x_1668_, v___x_1669_, v_type_1654_, v_type_1654_);
v___x_1671_ = l_Lean_Meta_Sym_synthInstance(v___x_1670_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1672_, lean_object* v_type_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1672_, v_type_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1682_, lean_object* v_type_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1682_, v_type_1683_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1696_, lean_object* v_type_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1696_, v_type_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec(v_a_1698_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1710_, lean_object* v_type_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1721_ = lean_box(0);
lean_inc(v_u_1710_);
v___x_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_u_1710_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1723_, 0, v_u_1710_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1720_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Lean_mkConst(v___x_1719_, v___x_1724_);
v___x_1726_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1711_);
v___x_1727_ = l_Lean_mkApp3(v___x_1725_, v___x_1726_, v_type_1711_, v_type_1711_);
v___x_1728_ = l_Lean_Meta_Sym_synthInstance(v___x_1727_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1729_, lean_object* v_type_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1729_, v_type_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1739_, lean_object* v_type_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1739_, v_type_1740_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1753_, lean_object* v_type_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1753_, v_type_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec(v_a_1755_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1767_, lean_object* v_parentInst_x3f_1768_, lean_object* v_childInst_x3f_1769_, lean_object* v_toFieldName_1770_, lean_object* v_u_1771_, lean_object* v_type_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1767_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1768_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1769_) == 1)
{
lean_object* v_val_1783_; lean_object* v_val_1784_; lean_object* v_val_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_toField_1789_; lean_object* v___x_1790_; 
v_val_1783_ = lean_ctor_get(v_leInst_x3f_1767_, 0);
lean_inc(v_val_1783_);
lean_dec_ref_known(v_leInst_x3f_1767_, 1);
v_val_1784_ = lean_ctor_get(v_parentInst_x3f_1768_, 0);
lean_inc_n(v_val_1784_, 2);
lean_dec_ref_known(v_parentInst_x3f_1768_, 1);
v_val_1785_ = lean_ctor_get(v_childInst_x3f_1769_, 0);
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_u_1771_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_mkConst(v_toFieldName_1770_, v___x_1787_);
lean_inc(v_val_1785_);
v_toField_1789_ = l_Lean_mkApp3(v___x_1788_, v_type_1772_, v_val_1783_, v_val_1785_);
lean_inc_ref(v_toField_1789_);
v___x_1790_ = l_Lean_Meta_isDefEqD(v_val_1784_, v_toField_1789_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1821_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1821_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1821_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_unbox(v_a_1791_);
lean_dec(v_a_1791_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1798_; 
lean_del_object(v___x_1793_);
lean_dec_ref_known(v_childInst_x3f_1769_, 1);
v___x_1796_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1784_, v_toField_1789_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1773_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; uint8_t v_verbose_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v_verbose_1800_ = lean_ctor_get_uint8(v_a_1799_, 0);
lean_dec(v_a_1799_);
if (v_verbose_1800_ == 0)
{
lean_dec(v_a_1797_);
goto v___jp_1780_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Meta_Sym_reportIssue(v_a_1797_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_dec_ref_known(v___x_1801_, 1);
goto v___jp_1780_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1797_);
v_a_1810_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1798_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1798_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v___x_1819_; 
lean_dec_ref(v_toField_1789_);
lean_dec(v_val_1784_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v_childInst_x3f_1769_);
v___x_1819_ = v___x_1793_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_childInst_x3f_1769_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v_toField_1789_);
lean_dec(v_val_1784_);
lean_dec_ref_known(v_childInst_x3f_1769_, 1);
v_a_1822_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1790_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1790_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref_known(v_leInst_x3f_1767_, 1);
lean_dec_ref(v_type_1772_);
lean_dec(v_u_1771_);
lean_dec(v_toFieldName_1770_);
lean_dec(v_childInst_x3f_1769_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_parentInst_x3f_1768_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_parentInst_x3f_1768_, 0);
lean_dec(v_unused_1838_);
v___x_1831_ = v_parentInst_x3f_1768_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_parentInst_x3f_1768_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_type_1772_);
lean_dec(v_u_1771_);
lean_dec(v_toFieldName_1770_);
lean_dec(v_childInst_x3f_1769_);
lean_dec(v_parentInst_x3f_1768_);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_leInst_x3f_1767_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v_leInst_x3f_1767_, 0);
lean_dec(v_unused_1847_);
v___x_1840_ = v_leInst_x3f_1767_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v_leInst_x3f_1767_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref(v_type_1772_);
lean_dec(v_u_1771_);
lean_dec(v_toFieldName_1770_);
lean_dec(v_childInst_x3f_1769_);
lean_dec(v_parentInst_x3f_1768_);
lean_dec(v_leInst_x3f_1767_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
v___jp_1780_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1850_, lean_object* v_parentInst_x3f_1851_, lean_object* v_childInst_x3f_1852_, lean_object* v_toFieldName_1853_, lean_object* v_u_1854_, lean_object* v_type_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1850_, v_parentInst_x3f_1851_, v_childInst_x3f_1852_, v_toFieldName_1853_, v_u_1854_, v_type_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1864_, lean_object* v_parentInst_x3f_1865_, lean_object* v_childInst_x3f_1866_, lean_object* v_toFieldName_1867_, lean_object* v_u_1868_, lean_object* v_type_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1864_, v_parentInst_x3f_1865_, v_childInst_x3f_1866_, v_toFieldName_1867_, v_u_1868_, v_type_1869_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1882_ = _args[0];
lean_object* v_parentInst_x3f_1883_ = _args[1];
lean_object* v_childInst_x3f_1884_ = _args[2];
lean_object* v_toFieldName_1885_ = _args[3];
lean_object* v_u_1886_ = _args[4];
lean_object* v_type_1887_ = _args[5];
lean_object* v_a_1888_ = _args[6];
lean_object* v_a_1889_ = _args[7];
lean_object* v_a_1890_ = _args[8];
lean_object* v_a_1891_ = _args[9];
lean_object* v_a_1892_ = _args[10];
lean_object* v_a_1893_ = _args[11];
lean_object* v_a_1894_ = _args[12];
lean_object* v_a_1895_ = _args[13];
lean_object* v_a_1896_ = _args[14];
lean_object* v_a_1897_ = _args[15];
lean_object* v_a_1898_ = _args[16];
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1882_, v_parentInst_x3f_1883_, v_childInst_x3f_1884_, v_toFieldName_1885_, v_u_1886_, v_type_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec(v_a_1888_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1900_, lean_object* v_inst_1901_, lean_object* v_toFieldName_1902_, lean_object* v_u_1903_, lean_object* v_type_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_toField_1913_; lean_object* v___x_1914_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_u_1903_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_mkConst(v_toFieldName_1902_, v___x_1911_);
v_toField_1913_ = l_Lean_mkAppB(v___x_1912_, v_type_1904_, v_inst_1901_);
v___x_1914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1900_, v_toField_1913_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1915_, lean_object* v_inst_1916_, lean_object* v_toFieldName_1917_, lean_object* v_u_1918_, lean_object* v_type_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1915_, v_inst_1916_, v_toFieldName_1917_, v_u_1918_, v_type_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1926_, lean_object* v_inst_1927_, lean_object* v_toFieldName_1928_, lean_object* v_u_1929_, lean_object* v_type_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1926_, v_inst_1927_, v_toFieldName_1928_, v_u_1929_, v_type_1930_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1943_, lean_object* v_inst_1944_, lean_object* v_toFieldName_1945_, lean_object* v_u_1946_, lean_object* v_type_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1943_, v_inst_1944_, v_toFieldName_1945_, v_u_1946_, v_type_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec(v_a_1948_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1960_, lean_object* v_inst_1961_, lean_object* v_toFieldName_1962_, lean_object* v_toHeteroName_1963_, lean_object* v_u_1964_, lean_object* v_type_1965_, lean_object* v_extraType_x3f_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_toField_1975_; 
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_u_1964_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_inc_ref(v___x_1973_);
v___x_1974_ = l_Lean_mkConst(v_toFieldName_1962_, v___x_1973_);
lean_inc_ref(v_type_1965_);
v_toField_1975_ = l_Lean_mkAppB(v___x_1974_, v_type_1965_, v_inst_1961_);
if (lean_obj_tag(v_extraType_x3f_1966_) == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = l_Lean_mkConst(v_toHeteroName_1963_, v___x_1973_);
v___x_1977_ = l_Lean_mkAppB(v___x_1976_, v_type_1965_, v_toField_1975_);
v___x_1978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1960_, v___x_1977_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1978_;
}
else
{
lean_object* v_val_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_val_1979_ = lean_ctor_get(v_extraType_x3f_1966_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v_extraType_x3f_1966_, 1);
v___x_1980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1973_);
v___x_1982_ = l_Lean_mkConst(v_toHeteroName_1963_, v___x_1981_);
v___x_1983_ = l_Lean_mkApp3(v___x_1982_, v_val_1979_, v_type_1965_, v_toField_1975_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1960_, v___x_1983_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1985_, lean_object* v_inst_1986_, lean_object* v_toFieldName_1987_, lean_object* v_toHeteroName_1988_, lean_object* v_u_1989_, lean_object* v_type_1990_, lean_object* v_extraType_x3f_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1985_, v_inst_1986_, v_toFieldName_1987_, v_toHeteroName_1988_, v_u_1989_, v_type_1990_, v_extraType_x3f_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1998_, lean_object* v_inst_1999_, lean_object* v_toFieldName_2000_, lean_object* v_toHeteroName_2001_, lean_object* v_u_2002_, lean_object* v_type_2003_, lean_object* v_extraType_x3f_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1998_, v_inst_1999_, v_toFieldName_2000_, v_toHeteroName_2001_, v_u_2002_, v_type_2003_, v_extraType_x3f_2004_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_2017_ = _args[0];
lean_object* v_inst_2018_ = _args[1];
lean_object* v_toFieldName_2019_ = _args[2];
lean_object* v_toHeteroName_2020_ = _args[3];
lean_object* v_u_2021_ = _args[4];
lean_object* v_type_2022_ = _args[5];
lean_object* v_extraType_x3f_2023_ = _args[6];
lean_object* v_a_2024_ = _args[7];
lean_object* v_a_2025_ = _args[8];
lean_object* v_a_2026_ = _args[9];
lean_object* v_a_2027_ = _args[10];
lean_object* v_a_2028_ = _args[11];
lean_object* v_a_2029_ = _args[12];
lean_object* v_a_2030_ = _args[13];
lean_object* v_a_2031_ = _args[14];
lean_object* v_a_2032_ = _args[15];
lean_object* v_a_2033_ = _args[16];
lean_object* v_a_2034_ = _args[17];
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2017_, v_inst_2018_, v_toFieldName_2019_, v_toHeteroName_2020_, v_u_2021_, v_type_2022_, v_extraType_x3f_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec(v_a_2024_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2040_, lean_object* v_type_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v_smulType_2057_; lean_object* v___x_2058_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2050_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2051_ = lean_box(0);
lean_inc(v_u_2040_);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_u_2040_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_u_2040_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2050_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_inc_ref(v___x_2054_);
v___x_2055_ = l_Lean_mkConst(v___x_2049_, v___x_2054_);
v___x_2056_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2041_, 2);
v_smulType_2057_ = l_Lean_mkApp3(v___x_2055_, v___x_2056_, v_type_2041_, v_type_2041_);
v___x_2058_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2057_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2095_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2095_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2095_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2090_; 
lean_del_object(v___x_2061_);
v_val_2063_ = lean_ctor_get(v_a_2059_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_a_2059_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2065_ = v_a_2059_;
v_isShared_2066_ = v_isSharedCheck_2090_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_a_2059_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2090_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2068_ = l_Lean_mkConst(v___x_2067_, v___x_2054_);
lean_inc_ref(v_type_2041_);
v___x_2069_ = l_Lean_mkApp4(v___x_2068_, v___x_2056_, v_type_2041_, v_type_2041_, v_val_2063_);
v___x_2070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2069_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2081_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_a_2071_);
v___x_2076_ = v___x_2065_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_del_object(v___x_2065_);
v_a_2082_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2070_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
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
else
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec(v_a_2059_);
lean_dec_ref_known(v___x_2054_, 2);
lean_dec_ref(v_type_2041_);
v___x_2091_ = lean_box(0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2091_);
v___x_2093_ = v___x_2061_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2054_, 2);
lean_dec_ref(v_type_2041_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2096_, lean_object* v_type_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2096_, v_type_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2106_, lean_object* v_type_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2106_, v_type_2107_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2120_, lean_object* v_type_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2120_, v_type_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec(v_a_2122_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2134_, lean_object* v_type_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_smulType_2151_; lean_object* v___x_2152_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2145_ = lean_box(0);
lean_inc(v_u_2134_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_u_2134_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_u_2134_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2144_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_inc_ref(v___x_2148_);
v___x_2149_ = l_Lean_mkConst(v___x_2143_, v___x_2148_);
v___x_2150_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2135_, 2);
v_smulType_2151_ = l_Lean_mkApp3(v___x_2149_, v___x_2150_, v_type_2135_, v_type_2135_);
v___x_2152_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2151_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2189_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2189_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2189_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
if (lean_obj_tag(v_a_2153_) == 1)
{
lean_object* v_val_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_2155_);
v_val_2157_ = lean_ctor_get(v_a_2153_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_a_2153_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2159_ = v_a_2153_;
v_isShared_2160_ = v_isSharedCheck_2184_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_val_2157_);
lean_dec(v_a_2153_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2184_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2162_ = l_Lean_mkConst(v___x_2161_, v___x_2148_);
lean_inc_ref(v_type_2135_);
v___x_2163_ = l_Lean_mkApp4(v___x_2162_, v___x_2150_, v_type_2135_, v_type_2135_, v_val_2157_);
v___x_2164_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2163_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2175_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2175_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2175_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v_a_2165_);
v___x_2170_ = v___x_2159_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
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
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2159_);
v_a_2176_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2164_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2164_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
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
lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec(v_a_2153_);
lean_dec_ref_known(v___x_2148_, 2);
lean_dec_ref(v_type_2135_);
v___x_2185_ = lean_box(0);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2185_);
v___x_2187_ = v___x_2155_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2148_, 2);
lean_dec_ref(v_type_2135_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2190_, lean_object* v_type_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2190_, v_type_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2200_, lean_object* v_type_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2200_, v_type_2201_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2214_, lean_object* v_type_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2214_, v_type_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v_ks_2232_; lean_object* v_vs_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2259_; 
v_ks_2232_ = lean_ctor_get(v_x_2228_, 0);
v_vs_2233_ = lean_ctor_get(v_x_2228_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_x_2228_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2235_ = v_x_2228_;
v_isShared_2236_ = v_isSharedCheck_2259_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_vs_2233_);
lean_inc(v_ks_2232_);
lean_dec(v_x_2228_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2259_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_array_get_size(v_ks_2232_);
v___x_2238_ = lean_nat_dec_lt(v_x_2229_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec(v_x_2229_);
v___x_2239_ = lean_array_push(v_ks_2232_, v_x_2230_);
v___x_2240_ = lean_array_push(v_vs_2233_, v_x_2231_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v___x_2240_);
lean_ctor_set(v___x_2235_, 0, v___x_2239_);
v___x_2242_ = v___x_2235_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v_k_x27_2244_; size_t v___x_2245_; size_t v___x_2246_; uint8_t v___x_2247_; 
v_k_x27_2244_ = lean_array_fget_borrowed(v_ks_2232_, v_x_2229_);
v___x_2245_ = lean_ptr_addr(v_x_2230_);
v___x_2246_ = lean_ptr_addr(v_k_x27_2244_);
v___x_2247_ = lean_usize_dec_eq(v___x_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2249_; 
if (v_isShared_2236_ == 0)
{
v___x_2249_ = v___x_2235_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_ks_2232_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_vs_2233_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v_x_2229_, v___x_2250_);
lean_dec(v_x_2229_);
v_x_2228_ = v___x_2249_;
v_x_2229_ = v___x_2251_;
goto _start;
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2254_ = lean_array_fset(v_ks_2232_, v_x_2229_, v_x_2230_);
v___x_2255_ = lean_array_fset(v_vs_2233_, v_x_2229_, v_x_2231_);
lean_dec(v_x_2229_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v___x_2255_);
lean_ctor_set(v___x_2235_, 0, v___x_2254_);
v___x_2257_ = v___x_2235_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2260_, lean_object* v_k_2261_, lean_object* v_v_2262_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2260_, v___x_2263_, v_k_2261_, v_v_2262_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2266_, size_t v_x_2267_, size_t v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_es_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v_j_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_es_2271_ = lean_ctor_get(v_x_2266_, 0);
v___x_2272_ = ((size_t)31ULL);
v___x_2273_ = lean_usize_land(v_x_2267_, v___x_2272_);
v_j_2274_ = lean_usize_to_nat(v___x_2273_);
v___x_2275_ = lean_array_get_size(v_es_2271_);
v___x_2276_ = lean_nat_dec_lt(v_j_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_dec(v_j_2274_);
lean_dec(v_x_2270_);
lean_dec_ref(v_x_2269_);
return v_x_2266_;
}
else
{
lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2317_; 
lean_inc_ref(v_es_2271_);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_x_2266_, 0);
lean_dec(v_unused_2318_);
v___x_2278_ = v_x_2266_;
v_isShared_2279_ = v_isSharedCheck_2317_;
goto v_resetjp_2277_;
}
else
{
lean_dec(v_x_2266_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2317_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_v_2280_; lean_object* v___x_2281_; lean_object* v_xs_x27_2282_; lean_object* v___y_2284_; 
v_v_2280_ = lean_array_fget(v_es_2271_, v_j_2274_);
v___x_2281_ = lean_box(0);
v_xs_x27_2282_ = lean_array_fset(v_es_2271_, v_j_2274_, v___x_2281_);
switch(lean_obj_tag(v_v_2280_))
{
case 0:
{
lean_object* v_key_2289_; lean_object* v_val_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2302_; 
v_key_2289_ = lean_ctor_get(v_v_2280_, 0);
v_val_2290_ = lean_ctor_get(v_v_2280_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_v_2280_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2292_ = v_v_2280_;
v_isShared_2293_ = v_isSharedCheck_2302_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_val_2290_);
lean_inc(v_key_2289_);
lean_dec(v_v_2280_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2302_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
size_t v___x_2294_; size_t v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = lean_ptr_addr(v_x_2269_);
v___x_2295_ = lean_ptr_addr(v_key_2289_);
v___x_2296_ = lean_usize_dec_eq(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_del_object(v___x_2292_);
v___x_2297_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2289_, v_val_2290_, v_x_2269_, v_x_2270_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
v___y_2284_ = v___x_2298_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2300_; 
lean_dec(v_val_2290_);
lean_dec(v_key_2289_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v_x_2270_);
lean_ctor_set(v___x_2292_, 0, v_x_2269_);
v___x_2300_ = v___x_2292_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_x_2269_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_x_2270_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
v___y_2284_ = v___x_2300_;
goto v___jp_2283_;
}
}
}
}
case 1:
{
lean_object* v_node_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2315_; 
v_node_2303_ = lean_ctor_get(v_v_2280_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_v_2280_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2305_ = v_v_2280_;
v_isShared_2306_ = v_isSharedCheck_2315_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_node_2303_);
lean_dec(v_v_2280_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2315_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2307_ = ((size_t)5ULL);
v___x_2308_ = lean_usize_shift_right(v_x_2267_, v___x_2307_);
v___x_2309_ = ((size_t)1ULL);
v___x_2310_ = lean_usize_add(v_x_2268_, v___x_2309_);
v___x_2311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2303_, v___x_2308_, v___x_2310_, v_x_2269_, v_x_2270_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2311_);
v___x_2313_ = v___x_2305_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
v___y_2284_ = v___x_2313_;
goto v___jp_2283_;
}
}
}
default: 
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v_x_2269_);
lean_ctor_set(v___x_2316_, 1, v_x_2270_);
v___y_2284_ = v___x_2316_;
goto v___jp_2283_;
}
}
v___jp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_array_fset(v_xs_x27_2282_, v_j_2274_, v___y_2284_);
lean_dec(v_j_2274_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2285_);
v___x_2287_ = v___x_2278_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_object* v_ks_2319_; lean_object* v_vs_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2338_; 
v_ks_2319_ = lean_ctor_get(v_x_2266_, 0);
v_vs_2320_ = lean_ctor_get(v_x_2266_, 1);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2322_ = v_x_2266_;
v_isShared_2323_ = v_isSharedCheck_2338_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_vs_2320_);
lean_inc(v_ks_2319_);
lean_dec(v_x_2266_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2338_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_ks_2319_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_vs_2320_);
v___x_2325_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v_newNode_2326_; size_t v___x_2327_; uint8_t v___x_2328_; 
v_newNode_2326_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2325_, v_x_2269_, v_x_2270_);
v___x_2327_ = ((size_t)7ULL);
v___x_2328_ = lean_usize_dec_le(v___x_2327_, v_x_2268_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2326_);
v___x_2330_ = lean_unsigned_to_nat(4u);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
lean_dec(v___x_2329_);
if (v___x_2331_ == 0)
{
lean_object* v_ks_2332_; lean_object* v_vs_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_ks_2332_ = lean_ctor_get(v_newNode_2326_, 0);
lean_inc_ref(v_ks_2332_);
v_vs_2333_ = lean_ctor_get(v_newNode_2326_, 1);
lean_inc_ref(v_vs_2333_);
lean_dec_ref(v_newNode_2326_);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2268_, v_ks_2332_, v_vs_2333_, v___x_2334_, v___x_2335_);
lean_dec_ref(v_vs_2333_);
lean_dec_ref(v_ks_2332_);
return v___x_2336_;
}
else
{
return v_newNode_2326_;
}
}
else
{
return v_newNode_2326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2339_, lean_object* v_keys_2340_, lean_object* v_vals_2341_, lean_object* v_i_2342_, lean_object* v_entries_2343_){
_start:
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_array_get_size(v_keys_2340_);
v___x_2345_ = lean_nat_dec_lt(v_i_2342_, v___x_2344_);
if (v___x_2345_ == 0)
{
lean_dec(v_i_2342_);
return v_entries_2343_;
}
else
{
lean_object* v_k_2346_; lean_object* v_v_2347_; size_t v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; uint64_t v___x_2351_; size_t v_h_2352_; size_t v___x_2353_; lean_object* v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; size_t v___x_2357_; size_t v_h_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_k_2346_ = lean_array_fget_borrowed(v_keys_2340_, v_i_2342_);
v_v_2347_ = lean_array_fget_borrowed(v_vals_2341_, v_i_2342_);
v___x_2348_ = lean_ptr_addr(v_k_2346_);
v___x_2349_ = ((size_t)3ULL);
v___x_2350_ = lean_usize_shift_right(v___x_2348_, v___x_2349_);
v___x_2351_ = lean_usize_to_uint64(v___x_2350_);
v_h_2352_ = lean_uint64_to_usize(v___x_2351_);
v___x_2353_ = ((size_t)5ULL);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_sub(v_depth_2339_, v___x_2355_);
v___x_2357_ = lean_usize_mul(v___x_2353_, v___x_2356_);
v_h_2358_ = lean_usize_shift_right(v_h_2352_, v___x_2357_);
v___x_2359_ = lean_nat_add(v_i_2342_, v___x_2354_);
lean_dec(v_i_2342_);
lean_inc(v_v_2347_);
lean_inc(v_k_2346_);
v___x_2360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2343_, v_h_2358_, v_depth_2339_, v_k_2346_, v_v_2347_);
v_i_2342_ = v___x_2359_;
v_entries_2343_ = v___x_2360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2362_, lean_object* v_keys_2363_, lean_object* v_vals_2364_, lean_object* v_i_2365_, lean_object* v_entries_2366_){
_start:
{
size_t v_depth_boxed_2367_; lean_object* v_res_2368_; 
v_depth_boxed_2367_ = lean_unbox_usize(v_depth_2362_);
lean_dec(v_depth_2362_);
v_res_2368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2367_, v_keys_2363_, v_vals_2364_, v_i_2365_, v_entries_2366_);
lean_dec_ref(v_vals_2364_);
lean_dec_ref(v_keys_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
size_t v_x_526656__boxed_2374_; size_t v_x_526657__boxed_2375_; lean_object* v_res_2376_; 
v_x_526656__boxed_2374_ = lean_unbox_usize(v_x_2370_);
lean_dec(v_x_2370_);
v_x_526657__boxed_2375_ = lean_unbox_usize(v_x_2371_);
lean_dec(v_x_2371_);
v_res_2376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2369_, v_x_526656__boxed_2374_, v_x_526657__boxed_2375_, v_x_2372_, v_x_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
size_t v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; uint64_t v___x_2383_; size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2380_ = lean_ptr_addr(v_x_2378_);
v___x_2381_ = ((size_t)3ULL);
v___x_2382_ = lean_usize_shift_right(v___x_2380_, v___x_2381_);
v___x_2383_ = lean_usize_to_uint64(v___x_2382_);
v___x_2384_ = lean_uint64_to_usize(v___x_2383_);
v___x_2385_ = ((size_t)1ULL);
v___x_2386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2377_, v___x_2384_, v___x_2385_, v_x_2378_, v_x_2379_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2387_, lean_object* v_s_2388_){
_start:
{
lean_object* v_structs_2389_; lean_object* v_typeIdOf_2390_; lean_object* v_exprToStructId_2391_; lean_object* v_exprToStructIdEntries_2392_; lean_object* v_forbiddenNatModules_2393_; lean_object* v_natStructs_2394_; lean_object* v_natTypeIdOf_2395_; lean_object* v_exprToNatStructId_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2405_; 
v_structs_2389_ = lean_ctor_get(v_s_2388_, 0);
v_typeIdOf_2390_ = lean_ctor_get(v_s_2388_, 1);
v_exprToStructId_2391_ = lean_ctor_get(v_s_2388_, 2);
v_exprToStructIdEntries_2392_ = lean_ctor_get(v_s_2388_, 3);
v_forbiddenNatModules_2393_ = lean_ctor_get(v_s_2388_, 4);
v_natStructs_2394_ = lean_ctor_get(v_s_2388_, 5);
v_natTypeIdOf_2395_ = lean_ctor_get(v_s_2388_, 6);
v_exprToNatStructId_2396_ = lean_ctor_get(v_s_2388_, 7);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_s_2388_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2398_ = v_s_2388_;
v_isShared_2399_ = v_isSharedCheck_2405_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_exprToNatStructId_2396_);
lean_inc(v_natTypeIdOf_2395_);
lean_inc(v_natStructs_2394_);
lean_inc(v_forbiddenNatModules_2393_);
lean_inc(v_exprToStructIdEntries_2392_);
lean_inc(v_exprToStructId_2391_);
lean_inc(v_typeIdOf_2390_);
lean_inc(v_structs_2389_);
lean_dec(v_s_2388_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2405_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = lean_box(0);
v___x_2401_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2393_, v_type_2387_, v___x_2400_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 4, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_structs_2389_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_typeIdOf_2390_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_exprToStructId_2391_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_exprToStructIdEntries_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2404_, 5, v_natStructs_2394_);
lean_ctor_set(v_reuseFailAlloc_2404_, 6, v_natTypeIdOf_2395_);
lean_ctor_set(v_reuseFailAlloc_2404_, 7, v_exprToNatStructId_2396_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v_a_2406_, lean_object* v_00___2407_){
_start:
{
if (lean_obj_tag(v_a_2406_) == 0)
{
uint8_t v___x_2408_; 
v___x_2408_ = 0;
return v___x_2408_;
}
else
{
uint8_t v___x_2409_; 
v___x_2409_ = 1;
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object* v_a_2410_, lean_object* v_00___2411_){
_start:
{
uint8_t v_res_2412_; lean_object* v_r_2413_; 
v_res_2412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2410_, v_00___2411_);
lean_dec(v_a_2410_);
v_r_2413_ = lean_box(v_res_2412_);
return v_r_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v___x_2414_, lean_object* v_s_2415_){
_start:
{
lean_object* v_structs_2416_; lean_object* v_typeIdOf_2417_; lean_object* v_exprToStructId_2418_; lean_object* v_exprToStructIdEntries_2419_; lean_object* v_forbiddenNatModules_2420_; lean_object* v_natStructs_2421_; lean_object* v_natTypeIdOf_2422_; lean_object* v_exprToNatStructId_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v_structs_2416_ = lean_ctor_get(v_s_2415_, 0);
v_typeIdOf_2417_ = lean_ctor_get(v_s_2415_, 1);
v_exprToStructId_2418_ = lean_ctor_get(v_s_2415_, 2);
v_exprToStructIdEntries_2419_ = lean_ctor_get(v_s_2415_, 3);
v_forbiddenNatModules_2420_ = lean_ctor_get(v_s_2415_, 4);
v_natStructs_2421_ = lean_ctor_get(v_s_2415_, 5);
v_natTypeIdOf_2422_ = lean_ctor_get(v_s_2415_, 6);
v_exprToNatStructId_2423_ = lean_ctor_get(v_s_2415_, 7);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_s_2415_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v_s_2415_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_exprToNatStructId_2423_);
lean_inc(v_natTypeIdOf_2422_);
lean_inc(v_natStructs_2421_);
lean_inc(v_forbiddenNatModules_2420_);
lean_inc(v_exprToStructIdEntries_2419_);
lean_inc(v_exprToStructId_2418_);
lean_inc(v_typeIdOf_2417_);
lean_inc(v_structs_2416_);
lean_dec(v_s_2415_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_array_push(v_structs_2416_, v___x_2414_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_typeIdOf_2417_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_exprToStructId_2418_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_exprToStructIdEntries_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_forbiddenNatModules_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 5, v_natStructs_2421_);
lean_ctor_set(v_reuseFailAlloc_2430_, 6, v_natTypeIdOf_2422_);
lean_ctor_set(v_reuseFailAlloc_2430_, 7, v_exprToNatStructId_2423_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_unsigned_to_nat(32u);
v___x_2439_ = lean_mk_empty_array_with_capacity(v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = l_Lean_mkRawNatLit(v___x_2465_);
return v___x_2466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = l_Lean_Int_mkType;
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = l_Lean_Nat_mkType;
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___y_2565_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___x_2630_; 
lean_inc_ref(v_type_2552_);
v___x_2630_ = l_Lean_Meta_getDecLevel_x3f(v_type_2552_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_3548_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_3548_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_3548_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
if (lean_obj_tag(v_a_2631_) == 1)
{
lean_object* v_val_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_3543_; 
lean_del_object(v___x_2633_);
v_val_2635_ = lean_ctor_get(v_a_2631_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_a_2631_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_2637_ = v_a_2631_;
v_isShared_2638_ = v_isSharedCheck_3543_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_val_2635_);
lean_dec(v_a_2631_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_3543_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; 
lean_inc_ref(v_type_2552_);
v___x_2639_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_3542_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_3542_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_3542_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2645_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2644_, v_val_2635_, v_type_2552_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2647_, v_val_2635_, v_type_2552_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc_n(v_a_2649_, 2);
lean_dec_ref_known(v___x_2648_, 1);
lean_inc(v_a_2646_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2650_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_2649_, v_a_2646_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; uint8_t v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v_homomulFn_x3f_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; uint8_t v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v_ltFn_x3f_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; uint8_t v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v_leFn_x3f_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_charInst_x3f_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___x_3163_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
lean_inc(v_a_2646_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3163_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_2646_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
lean_inc(v_a_2646_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3165_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_2646_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
lean_inc(v_a_2646_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3167_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_2646_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; uint8_t v___y_3190_; lean_object* v___x_3277_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3277_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2555_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; uint8_t v_ring_3279_; lean_object* v___f_3280_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; uint8_t v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; uint8_t v___y_3379_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v_ring_3279_ = lean_ctor_get_uint8(v_a_3278_, sizeof(void*)*14 + 21);
lean_dec(v_a_3278_);
lean_inc_ref(v_type_2552_);
v___f_3280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3280_, 0, v_type_2552_);
if (v_ring_3279_ == 0)
{
v___y_3379_ = v_ring_3279_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2640_, v___x_3464_);
if (v___x_3465_ == 0)
{
v___y_3379_ = v___x_3465_;
goto v___jp_3378_;
}
else
{
if (lean_obj_tag(v_a_3164_) == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v___x_3466_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3466_, v___f_3280_, v_a_2553_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3476_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_a_3477_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3467_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3467_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = 0;
v___y_3379_ = v___x_3485_;
goto v___jp_3378_;
}
}
}
v___jp_3281_:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3299_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; uint8_t v_ring_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v_ring_3305_ = lean_ctor_get_uint8(v_a_3304_, sizeof(void*)*14 + 21);
lean_dec(v_a_3304_);
if (v_ring_3305_ == 0)
{
lean_dec_ref(v___f_3280_);
v___y_3170_ = v___y_3282_;
v___y_3171_ = v___y_3283_;
v___y_3172_ = v___y_3284_;
v___y_3173_ = v___y_3285_;
v___y_3174_ = v___y_3286_;
v___y_3175_ = v___y_3287_;
v___y_3176_ = v___y_3289_;
v___y_3177_ = v___y_3302_;
v___y_3178_ = v___y_3290_;
v___y_3179_ = v___y_3291_;
v___y_3180_ = v___y_3292_;
v___y_3181_ = v___y_3293_;
v___y_3182_ = v___y_3294_;
v___y_3183_ = v___y_3295_;
v___y_3184_ = v___y_3297_;
v___y_3185_ = v___y_3296_;
v___y_3186_ = v___y_3298_;
v___y_3187_ = v___y_3299_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___y_3300_;
v___y_3190_ = v_ring_3305_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = lean_box(0);
v___x_3307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2640_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v___f_3280_);
v___y_3170_ = v___y_3282_;
v___y_3171_ = v___y_3283_;
v___y_3172_ = v___y_3284_;
v___y_3173_ = v___y_3285_;
v___y_3174_ = v___y_3286_;
v___y_3175_ = v___y_3287_;
v___y_3176_ = v___y_3289_;
v___y_3177_ = v___y_3302_;
v___y_3178_ = v___y_3290_;
v___y_3179_ = v___y_3291_;
v___y_3180_ = v___y_3292_;
v___y_3181_ = v___y_3293_;
v___y_3182_ = v___y_3294_;
v___y_3183_ = v___y_3295_;
v___y_3184_ = v___y_3297_;
v___y_3185_ = v___y_3296_;
v___y_3186_ = v___y_3298_;
v___y_3187_ = v___y_3299_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___y_3300_;
v___y_3190_ = v___x_3307_;
goto v___jp_3169_;
}
else
{
if (lean_obj_tag(v___y_3302_) == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3298_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v___x_3308_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3309_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3308_, v___f_3280_, v___y_3282_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3317_; 
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3318_);
v___x_3311_ = v___x_3309_;
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
else
{
lean_dec(v___x_3309_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3315_ = v___x_3311_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
v_a_3319_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3309_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3309_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_dec_ref(v___f_3280_);
v___y_3170_ = v___y_3282_;
v___y_3171_ = v___y_3283_;
v___y_3172_ = v___y_3284_;
v___y_3173_ = v___y_3285_;
v___y_3174_ = v___y_3286_;
v___y_3175_ = v___y_3287_;
v___y_3176_ = v___y_3289_;
v___y_3177_ = v___y_3302_;
v___y_3178_ = v___y_3290_;
v___y_3179_ = v___y_3291_;
v___y_3180_ = v___y_3292_;
v___y_3181_ = v___y_3293_;
v___y_3182_ = v___y_3294_;
v___y_3183_ = v___y_3295_;
v___y_3184_ = v___y_3297_;
v___y_3185_ = v___y_3296_;
v___y_3186_ = v___y_3298_;
v___y_3187_ = v___y_3299_;
v___y_3188_ = v___y_3301_;
v___y_3189_ = v___y_3300_;
v___y_3190_ = v___y_3288_;
goto v___jp_3169_;
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3298_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3327_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3303_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3303_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
v___jp_3335_:
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_box(0);
v___y_3282_ = v___y_3336_;
v___y_3283_ = v___y_3337_;
v___y_3284_ = v___y_3338_;
v___y_3285_ = v___y_3339_;
v___y_3286_ = v___y_3340_;
v___y_3287_ = v___y_3341_;
v___y_3288_ = v___y_3342_;
v___y_3289_ = v___y_3343_;
v___y_3290_ = v___y_3344_;
v___y_3291_ = v___y_3345_;
v___y_3292_ = v___y_3346_;
v___y_3293_ = v___y_3347_;
v___y_3294_ = v___y_3348_;
v___y_3295_ = v___y_3349_;
v___y_3296_ = v___y_3351_;
v___y_3297_ = v___y_3350_;
v___y_3298_ = v___y_3353_;
v___y_3299_ = v___y_3352_;
v___y_3300_ = v___y_3355_;
v___y_3301_ = v___y_3354_;
v___y_3302_ = v___x_3356_;
goto v___jp_3281_;
}
v___jp_3357_:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_box(0);
v___y_3336_ = v___y_3367_;
v___y_3337_ = v___x_3377_;
v___y_3338_ = v___y_3359_;
v___y_3339_ = v___y_3360_;
v___y_3340_ = v___y_3361_;
v___y_3341_ = v___y_3362_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3376_;
v___y_3344_ = v___y_3373_;
v___y_3345_ = v___y_3358_;
v___y_3346_ = v___y_3368_;
v___y_3347_ = v___y_3372_;
v___y_3348_ = v___y_3370_;
v___y_3349_ = v___y_3363_;
v___y_3350_ = v___y_3371_;
v___y_3351_ = v___y_3375_;
v___y_3352_ = v___y_3369_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___y_3366_;
v___y_3355_ = v___y_3374_;
goto v___jp_3335_;
}
v___jp_3378_:
{
lean_object* v___x_3380_; 
lean_inc(v_a_2640_);
v___x_3380_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2640_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_n(v_a_3381_, 2);
lean_dec_ref_known(v___x_3380_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_3381_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_n(v_a_3383_, 2);
lean_dec_ref_known(v___x_3382_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_3383_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3439_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3439_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3439_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
if (lean_obj_tag(v_a_3385_) == 1)
{
lean_object* v_val_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_del_object(v___x_3387_);
v_val_3389_ = lean_ctor_get(v_a_3385_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v_a_3385_, 1);
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3390_, v_val_2635_, v_type_2552_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc_n(v_a_3392_, 2);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3394_ = lean_box(0);
lean_inc_n(v_val_2635_, 3);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_val_2635_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
lean_inc_ref(v___x_3395_);
v___x_3396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_val_2635_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
lean_inc_ref(v___x_3396_);
v___x_3397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_val_2635_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
lean_inc_ref(v___x_3397_);
v___x_3398_ = l_Lean_mkConst(v___x_3393_, v___x_3397_);
lean_inc_ref_n(v_type_2552_, 3);
v___x_3399_ = l_Lean_mkApp4(v___x_3398_, v_type_2552_, v_type_2552_, v_type_2552_, v_a_3392_);
v___x_3400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3399_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3400_) == 0)
{
if (lean_obj_tag(v_a_2646_) == 1)
{
if (lean_obj_tag(v_a_3164_) == 1)
{
lean_object* v_a_3401_; lean_object* v_val_3402_; lean_object* v_val_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v_val_3402_ = lean_ctor_get(v_a_2646_, 0);
v_val_3403_ = lean_ctor_get(v_a_3164_, 0);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3395_);
v___x_3405_ = l_Lean_mkConst(v___x_3404_, v___x_3395_);
lean_inc(v_val_3403_);
lean_inc(v_val_3402_);
lean_inc(v_a_3392_);
lean_inc_ref(v_type_2552_);
v___x_3406_ = l_Lean_mkApp4(v___x_3405_, v_type_2552_, v_a_3392_, v_val_3402_, v_val_3403_);
v___x_3407_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3406_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 0)
{
lean_dec_ref_known(v_a_3164_, 1);
v___y_3336_ = v_a_2553_;
v___y_3337_ = v_a_3408_;
v___y_3338_ = v___x_3397_;
v___y_3339_ = v___x_3395_;
v___y_3340_ = v_val_3389_;
v___y_3341_ = v_a_3381_;
v___y_3342_ = v___y_3379_;
v___y_3343_ = v_a_2562_;
v___y_3344_ = v_a_2559_;
v___y_3345_ = v_a_3392_;
v___y_3346_ = v_a_2554_;
v___y_3347_ = v_a_2558_;
v___y_3348_ = v_a_2556_;
v___y_3349_ = v_a_3383_;
v___y_3350_ = v_a_2557_;
v___y_3351_ = v_a_2561_;
v___y_3352_ = v_a_2555_;
v___y_3353_ = v___x_3396_;
v___y_3354_ = v_a_3401_;
v___y_3355_ = v_a_2560_;
goto v___jp_3335_;
}
else
{
if (v___y_3379_ == 0)
{
v___y_3282_ = v_a_2553_;
v___y_3283_ = v_a_3408_;
v___y_3284_ = v___x_3397_;
v___y_3285_ = v___x_3395_;
v___y_3286_ = v_val_3389_;
v___y_3287_ = v_a_3381_;
v___y_3288_ = v___y_3379_;
v___y_3289_ = v_a_2562_;
v___y_3290_ = v_a_2559_;
v___y_3291_ = v_a_3392_;
v___y_3292_ = v_a_2554_;
v___y_3293_ = v_a_2558_;
v___y_3294_ = v_a_2556_;
v___y_3295_ = v_a_3383_;
v___y_3296_ = v_a_2561_;
v___y_3297_ = v_a_2557_;
v___y_3298_ = v___x_3396_;
v___y_3299_ = v_a_2555_;
v___y_3300_ = v_a_2560_;
v___y_3301_ = v_a_3401_;
v___y_3302_ = v_a_3164_;
goto v___jp_3281_;
}
else
{
lean_dec_ref_known(v_a_3164_, 1);
v___y_3336_ = v_a_2553_;
v___y_3337_ = v_a_3408_;
v___y_3338_ = v___x_3397_;
v___y_3339_ = v___x_3395_;
v___y_3340_ = v_val_3389_;
v___y_3341_ = v_a_3381_;
v___y_3342_ = v___y_3379_;
v___y_3343_ = v_a_2562_;
v___y_3344_ = v_a_2559_;
v___y_3345_ = v_a_3392_;
v___y_3346_ = v_a_2554_;
v___y_3347_ = v_a_2558_;
v___y_3348_ = v_a_2556_;
v___y_3349_ = v_a_3383_;
v___y_3350_ = v_a_2557_;
v___y_3351_ = v_a_2561_;
v___y_3352_ = v_a_2555_;
v___y_3353_ = v___x_3396_;
v___y_3354_ = v_a_3401_;
v___y_3355_ = v_a_2560_;
goto v___jp_3335_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_a_3401_);
lean_dec_ref_known(v_a_3164_, 1);
lean_dec_ref_known(v_a_2646_, 1);
lean_dec_ref_known(v___x_3397_, 2);
lean_dec_ref_known(v___x_3396_, 2);
lean_dec_ref_known(v___x_3395_, 2);
lean_dec(v_a_3392_);
lean_dec(v_val_3389_);
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3409_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3407_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; 
lean_dec(v_a_3164_);
v_a_3417_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3400_, 1);
v___y_3358_ = v_a_3392_;
v___y_3359_ = v___x_3397_;
v___y_3360_ = v___x_3395_;
v___y_3361_ = v_val_3389_;
v___y_3362_ = v_a_3381_;
v___y_3363_ = v_a_3383_;
v___y_3364_ = v___y_3379_;
v___y_3365_ = v___x_3396_;
v___y_3366_ = v_a_3417_;
v___y_3367_ = v_a_2553_;
v___y_3368_ = v_a_2554_;
v___y_3369_ = v_a_2555_;
v___y_3370_ = v_a_2556_;
v___y_3371_ = v_a_2557_;
v___y_3372_ = v_a_2558_;
v___y_3373_ = v_a_2559_;
v___y_3374_ = v_a_2560_;
v___y_3375_ = v_a_2561_;
v___y_3376_ = v_a_2562_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3418_; 
lean_dec(v_a_3164_);
v_a_3418_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3400_, 1);
v___y_3358_ = v_a_3392_;
v___y_3359_ = v___x_3397_;
v___y_3360_ = v___x_3395_;
v___y_3361_ = v_val_3389_;
v___y_3362_ = v_a_3381_;
v___y_3363_ = v_a_3383_;
v___y_3364_ = v___y_3379_;
v___y_3365_ = v___x_3396_;
v___y_3366_ = v_a_3418_;
v___y_3367_ = v_a_2553_;
v___y_3368_ = v_a_2554_;
v___y_3369_ = v_a_2555_;
v___y_3370_ = v_a_2556_;
v___y_3371_ = v_a_2557_;
v___y_3372_ = v_a_2558_;
v___y_3373_ = v_a_2559_;
v___y_3374_ = v_a_2560_;
v___y_3375_ = v_a_2561_;
v___y_3376_ = v_a_2562_;
goto v___jp_3357_;
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref_known(v___x_3397_, 2);
lean_dec_ref_known(v___x_3396_, 2);
lean_dec_ref_known(v___x_3395_, 2);
lean_dec(v_a_3392_);
lean_dec(v_val_3389_);
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3419_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3400_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3400_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_val_3389_);
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3427_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3391_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3391_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_dec(v_a_3385_);
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v___x_3435_ = lean_box(0);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3435_);
v___x_3437_ = v___x_3387_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3440_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3384_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3384_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_a_3381_);
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3448_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3382_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3382_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v___f_3280_);
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3456_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3380_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3380_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v_a_3168_);
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3486_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3277_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3277_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
v___jp_3169_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc(v___y_3177_);
lean_inc(v_a_2646_);
v___x_3192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2646_, v___y_3177_, v_a_3166_, v___x_3191_, v_val_2635_, v_type_2552_, v___y_3184_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc(v_a_2646_);
v___x_3195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2646_, v_a_3193_, v_a_3168_, v___x_3194_, v_val_2635_, v_type_2552_, v___y_3184_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3173_, 2);
v___x_3201_ = l_Lean_mkConst(v___x_3200_, v___y_3173_);
lean_inc_ref(v___y_3174_);
lean_inc_ref_n(v_type_2552_, 3);
v___x_3202_ = l_Lean_mkAppB(v___x_3201_, v_type_2552_, v___y_3174_);
v___x_3203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3205_ = l_Lean_mkConst(v___x_3204_, v___y_3173_);
lean_inc_ref(v___x_3202_);
v___x_3206_ = l_Lean_mkAppB(v___x_3205_, v_type_2552_, v___x_3202_);
lean_inc(v___y_3183_);
lean_inc(v_val_2635_);
v___x_3207_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2635_, v_type_2552_, v___y_3183_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3209_, v_val_2635_, v_type_2552_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2635_, v_type_2552_, v___y_3170_, v___y_3180_, v___y_3187_, v___y_3182_, v___y_3184_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
lean_inc(v___y_3177_);
lean_inc(v_a_2649_);
lean_inc(v_a_2646_);
lean_inc(v_a_3208_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3214_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2635_, v_type_2552_, v_a_3208_, v_a_2646_, v_a_2649_, v___y_3177_, v___y_3184_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3214_) == 0)
{
if (lean_obj_tag(v_a_3208_) == 1)
{
lean_object* v_a_3215_; lean_object* v_val_3216_; lean_object* v___x_3217_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v_val_3216_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v_a_3208_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_3217_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2635_, v_type_2552_, v_val_3216_, v___y_3170_, v___y_3180_, v___y_3187_, v___y_3182_, v___y_3184_, v___y_3181_, v___y_3178_, v___y_3189_, v___y_3185_, v___y_3176_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___y_2861_ = v_a_3215_;
v___y_2862_ = v___x_3199_;
v___y_2863_ = v___y_3172_;
v___y_2864_ = v___y_3171_;
v___y_2865_ = v___y_3173_;
v___y_2866_ = v___y_3174_;
v___y_2867_ = v___y_3175_;
v___y_2868_ = v___x_3203_;
v___y_2869_ = v___y_3177_;
v___y_2870_ = v___x_3206_;
v___y_2871_ = v_a_3213_;
v___y_2872_ = v___y_3179_;
v___y_2873_ = v___x_3197_;
v___y_2874_ = v___y_3190_;
v___y_2875_ = v_a_3196_;
v___y_2876_ = v___x_3198_;
v___y_2877_ = v_a_3211_;
v___y_2878_ = v___y_3183_;
v___y_2879_ = v___x_3202_;
v___y_2880_ = v___y_3186_;
v___y_2881_ = v___y_3188_;
v_charInst_x3f_2882_ = v_a_3218_;
v___y_2883_ = v___y_3170_;
v___y_2884_ = v___y_3180_;
v___y_2885_ = v___y_3187_;
v___y_2886_ = v___y_3182_;
v___y_2887_ = v___y_3184_;
v___y_2888_ = v___y_3181_;
v___y_2889_ = v___y_3178_;
v___y_2890_ = v___y_3189_;
v___y_2891_ = v___y_3185_;
v___y_2892_ = v___y_3176_;
goto v___jp_2860_;
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_a_3215_);
lean_dec(v_a_3213_);
lean_dec(v_a_3211_);
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
lean_dec(v_a_3196_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3219_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
lean_dec(v_a_3208_);
v_a_3227_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3228_ = lean_box(0);
v___y_2861_ = v_a_3227_;
v___y_2862_ = v___x_3199_;
v___y_2863_ = v___y_3172_;
v___y_2864_ = v___y_3171_;
v___y_2865_ = v___y_3173_;
v___y_2866_ = v___y_3174_;
v___y_2867_ = v___y_3175_;
v___y_2868_ = v___x_3203_;
v___y_2869_ = v___y_3177_;
v___y_2870_ = v___x_3206_;
v___y_2871_ = v_a_3213_;
v___y_2872_ = v___y_3179_;
v___y_2873_ = v___x_3197_;
v___y_2874_ = v___y_3190_;
v___y_2875_ = v_a_3196_;
v___y_2876_ = v___x_3198_;
v___y_2877_ = v_a_3211_;
v___y_2878_ = v___y_3183_;
v___y_2879_ = v___x_3202_;
v___y_2880_ = v___y_3186_;
v___y_2881_ = v___y_3188_;
v_charInst_x3f_2882_ = v___x_3228_;
v___y_2883_ = v___y_3170_;
v___y_2884_ = v___y_3180_;
v___y_2885_ = v___y_3187_;
v___y_2886_ = v___y_3182_;
v___y_2887_ = v___y_3184_;
v___y_2888_ = v___y_3181_;
v___y_2889_ = v___y_3178_;
v___y_2890_ = v___y_3189_;
v___y_2891_ = v___y_3185_;
v___y_2892_ = v___y_3176_;
goto v___jp_2860_;
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_a_3213_);
lean_dec(v_a_3211_);
lean_dec(v_a_3208_);
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
lean_dec(v_a_3196_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3229_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3214_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3214_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_a_3211_);
lean_dec(v_a_3208_);
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
lean_dec(v_a_3196_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3237_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3212_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3212_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_a_3208_);
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
lean_dec(v_a_3196_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3245_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3210_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3210_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___x_3206_);
lean_dec_ref(v___x_3202_);
lean_dec(v_a_3196_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3253_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3207_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3207_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3261_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3195_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3195_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3177_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_a_3168_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3269_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3192_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3192_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3166_);
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3494_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3167_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3167_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3164_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3502_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3165_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3165_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3510_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3163_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3163_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
v___jp_2652_:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2678_, v___y_2686_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v_structs_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; size_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v_structs_2690_ = lean_ctor_get(v_a_2689_, 0);
lean_inc_ref(v_structs_2690_);
lean_dec(v_a_2689_);
v___x_2691_ = lean_array_get_size(v_structs_2690_);
lean_dec_ref(v_structs_2690_);
v___x_2692_ = lean_unsigned_to_nat(32u);
v___x_2693_ = lean_mk_empty_array_with_capacity(v___x_2692_);
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2695_ = ((size_t)5ULL);
lean_inc(v___y_2667_);
v___x_2696_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2693_);
lean_ctor_set(v___x_2696_, 2, v___y_2667_);
lean_ctor_set(v___x_2696_, 3, v___y_2667_);
lean_ctor_set_usize(v___x_2696_, 4, v___x_2695_);
v___x_2697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_box(0);
lean_inc_ref_n(v___x_2696_, 7);
lean_inc(v___y_2663_);
lean_inc(v___y_2658_);
lean_inc(v___y_2668_);
lean_inc(v___y_2656_);
lean_inc(v___y_2670_);
v___x_2700_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2700_, 0, v___x_2691_);
lean_ctor_set(v___x_2700_, 1, v_a_2640_);
lean_ctor_set(v___x_2700_, 2, v_type_2552_);
lean_ctor_set(v___x_2700_, 3, v_val_2635_);
lean_ctor_set(v___x_2700_, 4, v___y_2659_);
lean_ctor_set(v___x_2700_, 5, v_a_2646_);
lean_ctor_set(v___x_2700_, 6, v_a_2649_);
lean_ctor_set(v___x_2700_, 7, v_a_2651_);
lean_ctor_set(v___x_2700_, 8, v___y_2662_);
lean_ctor_set(v___x_2700_, 9, v___y_2657_);
lean_ctor_set(v___x_2700_, 10, v___y_2666_);
lean_ctor_set(v___x_2700_, 11, v___y_2661_);
lean_ctor_set(v___x_2700_, 12, v___y_2670_);
lean_ctor_set(v___x_2700_, 13, v___y_2660_);
lean_ctor_set(v___x_2700_, 14, v___y_2656_);
lean_ctor_set(v___x_2700_, 15, v___y_2668_);
lean_ctor_set(v___x_2700_, 16, v___y_2658_);
lean_ctor_set(v___x_2700_, 17, v___y_2671_);
lean_ctor_set(v___x_2700_, 18, v___y_2672_);
lean_ctor_set(v___x_2700_, 19, v___y_2663_);
lean_ctor_set(v___x_2700_, 20, v___y_2673_);
lean_ctor_set(v___x_2700_, 21, v___y_2676_);
lean_ctor_set(v___x_2700_, 22, v___y_2675_);
lean_ctor_set(v___x_2700_, 23, v___y_2655_);
lean_ctor_set(v___x_2700_, 24, v___y_2654_);
lean_ctor_set(v___x_2700_, 25, v___y_2665_);
lean_ctor_set(v___x_2700_, 26, v___y_2653_);
lean_ctor_set(v___x_2700_, 27, v_homomulFn_x3f_2677_);
lean_ctor_set(v___x_2700_, 28, v___y_2669_);
lean_ctor_set(v___x_2700_, 29, v___y_2674_);
lean_ctor_set(v___x_2700_, 30, v___x_2696_);
lean_ctor_set(v___x_2700_, 31, v___x_2697_);
lean_ctor_set(v___x_2700_, 32, v___x_2696_);
lean_ctor_set(v___x_2700_, 33, v___x_2696_);
lean_ctor_set(v___x_2700_, 34, v___x_2696_);
lean_ctor_set(v___x_2700_, 35, v___x_2696_);
lean_ctor_set(v___x_2700_, 36, v___x_2698_);
lean_ctor_set(v___x_2700_, 37, v___x_2697_);
lean_ctor_set(v___x_2700_, 38, v___x_2696_);
lean_ctor_set(v___x_2700_, 39, v___x_2699_);
lean_ctor_set(v___x_2700_, 40, v___x_2696_);
lean_ctor_set(v___x_2700_, 41, v___x_2696_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*42, v___y_2664_);
v___f_2701_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2701_, 0, v___x_2700_);
v___x_2702_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2702_, v___f_2701_, v___y_2678_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
if (lean_obj_tag(v___y_2663_) == 1)
{
if (lean_obj_tag(v___y_2670_) == 0)
{
lean_dec_ref_known(v___y_2663_, 1);
lean_dec(v___y_2668_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
v___y_2565_ = v___x_2691_;
goto v___jp_2564_;
}
else
{
lean_dec_ref_known(v___y_2670_, 1);
if (lean_obj_tag(v___y_2656_) == 0)
{
if (v___y_2664_ == 0)
{
if (lean_obj_tag(v___y_2668_) == 0)
{
lean_object* v_val_2704_; uint8_t v___x_2705_; 
v_val_2704_ = lean_ctor_get(v___y_2663_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v___y_2663_, 1);
v___x_2705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2658_);
lean_dec(v___y_2658_);
if (v___x_2705_ == 0)
{
lean_dec(v_val_2704_);
v___y_2565_ = v___x_2691_;
goto v___jp_2564_;
}
else
{
v___y_2580_ = v___y_2682_;
v___y_2581_ = v_val_2704_;
v___y_2582_ = v___y_2683_;
v___y_2583_ = v___y_2684_;
v___y_2584_ = v___y_2680_;
v___y_2585_ = v___y_2687_;
v___y_2586_ = v___y_2664_;
v___y_2587_ = v___x_2691_;
v___y_2588_ = v___y_2679_;
v___y_2589_ = v___y_2681_;
v___y_2590_ = v___y_2685_;
v___y_2591_ = v___y_2678_;
v___y_2592_ = v___y_2686_;
goto v___jp_2579_;
}
}
else
{
lean_object* v_val_2706_; 
lean_dec_ref_known(v___y_2668_, 1);
lean_dec(v___y_2658_);
v_val_2706_ = lean_ctor_get(v___y_2663_, 0);
lean_inc(v_val_2706_);
lean_dec_ref_known(v___y_2663_, 1);
v___y_2580_ = v___y_2682_;
v___y_2581_ = v_val_2706_;
v___y_2582_ = v___y_2683_;
v___y_2583_ = v___y_2684_;
v___y_2584_ = v___y_2680_;
v___y_2585_ = v___y_2687_;
v___y_2586_ = v___y_2664_;
v___y_2587_ = v___x_2691_;
v___y_2588_ = v___y_2679_;
v___y_2589_ = v___y_2681_;
v___y_2590_ = v___y_2685_;
v___y_2591_ = v___y_2678_;
v___y_2592_ = v___y_2686_;
goto v___jp_2579_;
}
}
else
{
lean_object* v_val_2707_; 
lean_dec(v___y_2668_);
lean_dec(v___y_2658_);
v_val_2707_ = lean_ctor_get(v___y_2663_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v___y_2663_, 1);
v___y_2605_ = v___y_2682_;
v___y_2606_ = v_val_2707_;
v___y_2607_ = v___y_2683_;
v___y_2608_ = v___y_2684_;
v___y_2609_ = v___y_2680_;
v___y_2610_ = v___y_2687_;
v___y_2611_ = v___y_2664_;
v___y_2612_ = v___x_2691_;
v___y_2613_ = v___y_2679_;
v___y_2614_ = v___y_2681_;
v___y_2615_ = v___y_2685_;
v___y_2616_ = v___y_2678_;
v___y_2617_ = v___y_2686_;
goto v___jp_2604_;
}
}
else
{
lean_object* v_val_2708_; 
lean_dec_ref_known(v___y_2656_, 1);
lean_dec(v___y_2668_);
lean_dec(v___y_2658_);
v_val_2708_ = lean_ctor_get(v___y_2663_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v___y_2663_, 1);
v___y_2605_ = v___y_2682_;
v___y_2606_ = v_val_2708_;
v___y_2607_ = v___y_2683_;
v___y_2608_ = v___y_2684_;
v___y_2609_ = v___y_2680_;
v___y_2610_ = v___y_2687_;
v___y_2611_ = v___y_2664_;
v___y_2612_ = v___x_2691_;
v___y_2613_ = v___y_2679_;
v___y_2614_ = v___y_2681_;
v___y_2615_ = v___y_2685_;
v___y_2616_ = v___y_2678_;
v___y_2617_ = v___y_2686_;
goto v___jp_2604_;
}
}
}
else
{
lean_dec(v___y_2670_);
lean_dec(v___y_2668_);
lean_dec(v___y_2663_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
v___y_2565_ = v___x_2691_;
goto v___jp_2564_;
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v___y_2670_);
lean_dec(v___y_2668_);
lean_dec(v___y_2663_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
v_a_2709_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2703_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2703_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_homomulFn_x3f_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_dec(v_a_2640_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2717_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2688_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2688_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
v___jp_2725_:
{
lean_object* v___x_2760_; 
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2635_, v_type_2552_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2635_, v_type_2552_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2762_) == 0)
{
if (lean_obj_tag(v___y_2733_) == 0)
{
lean_object* v_a_2763_; 
lean_dec(v___y_2729_);
lean_del_object(v___x_2637_);
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___y_2653_ = v_a_2763_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2730_;
v___y_2658_ = v___y_2731_;
v___y_2659_ = v___y_2732_;
v___y_2660_ = v___y_2733_;
v___y_2661_ = v___y_2735_;
v___y_2662_ = v___y_2736_;
v___y_2663_ = v___y_2737_;
v___y_2664_ = v___y_2738_;
v___y_2665_ = v_a_2761_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2743_;
v___y_2670_ = v___y_2742_;
v___y_2671_ = v___y_2745_;
v___y_2672_ = v___y_2744_;
v___y_2673_ = v___y_2746_;
v___y_2674_ = v___y_2747_;
v___y_2675_ = v___y_2748_;
v___y_2676_ = v_ltFn_x3f_2749_;
v_homomulFn_x3f_2677_ = v___y_2734_;
v___y_2678_ = v___y_2750_;
v___y_2679_ = v___y_2751_;
v___y_2680_ = v___y_2752_;
v___y_2681_ = v___y_2753_;
v___y_2682_ = v___y_2754_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v___y_2756_;
v___y_2685_ = v___y_2757_;
v___y_2686_ = v___y_2758_;
v___y_2687_ = v___y_2759_;
goto v___jp_2652_;
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v___y_2734_);
v_a_2764_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2765_, v_val_2635_, v_type_2552_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2769_ = l_Lean_mkConst(v___x_2768_, v___y_2729_);
lean_inc_ref_n(v_type_2552_, 3);
v___x_2770_ = l_Lean_mkApp4(v___x_2769_, v_type_2552_, v_type_2552_, v_type_2552_, v_a_2767_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2770_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_a_2772_);
v___x_2774_ = v___x_2637_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
v___y_2653_ = v_a_2764_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2730_;
v___y_2658_ = v___y_2731_;
v___y_2659_ = v___y_2732_;
v___y_2660_ = v___y_2733_;
v___y_2661_ = v___y_2735_;
v___y_2662_ = v___y_2736_;
v___y_2663_ = v___y_2737_;
v___y_2664_ = v___y_2738_;
v___y_2665_ = v_a_2761_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2743_;
v___y_2670_ = v___y_2742_;
v___y_2671_ = v___y_2745_;
v___y_2672_ = v___y_2744_;
v___y_2673_ = v___y_2746_;
v___y_2674_ = v___y_2747_;
v___y_2675_ = v___y_2748_;
v___y_2676_ = v_ltFn_x3f_2749_;
v_homomulFn_x3f_2677_ = v___x_2774_;
v___y_2678_ = v___y_2750_;
v___y_2679_ = v___y_2751_;
v___y_2680_ = v___y_2752_;
v___y_2681_ = v___y_2753_;
v___y_2682_ = v___y_2754_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v___y_2756_;
v___y_2685_ = v___y_2757_;
v___y_2686_ = v___y_2758_;
v___y_2687_ = v___y_2759_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2764_);
lean_dec_ref_known(v___y_2733_, 1);
lean_dec(v_a_2761_);
lean_dec(v_ltFn_x3f_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2776_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2771_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2771_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref_known(v___y_2733_, 1);
lean_dec(v_a_2764_);
lean_dec(v_a_2761_);
lean_dec(v_ltFn_x3f_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2784_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2766_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2766_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2761_);
lean_dec(v_ltFn_x3f_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2792_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2762_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2762_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_ltFn_x3f_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2800_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2760_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2760_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
v___jp_2808_:
{
if (lean_obj_tag(v_a_2649_) == 1)
{
lean_object* v_val_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_val_2843_ = lean_ctor_get(v_a_2649_, 0);
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2845_ = l_Lean_mkConst(v___x_2844_, v___y_2815_);
lean_inc(v_val_2843_);
lean_inc_ref(v_type_2552_);
v___x_2846_ = l_Lean_mkAppB(v___x_2845_, v_type_2552_, v_val_2843_);
v___x_2847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2846_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 1);
lean_ctor_set(v___x_2642_, 0, v_a_2848_);
v___x_2850_ = v___x_2642_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
v___y_2730_ = v___y_2813_;
v___y_2731_ = v___y_2814_;
v___y_2732_ = v___y_2816_;
v___y_2733_ = v___y_2817_;
v___y_2734_ = v___y_2818_;
v___y_2735_ = v___y_2819_;
v___y_2736_ = v___y_2820_;
v___y_2737_ = v___y_2821_;
v___y_2738_ = v___y_2822_;
v___y_2739_ = v___y_2823_;
v___y_2740_ = v___y_2824_;
v___y_2741_ = v___y_2825_;
v___y_2742_ = v___y_2827_;
v___y_2743_ = v___y_2826_;
v___y_2744_ = v___y_2829_;
v___y_2745_ = v___y_2828_;
v___y_2746_ = v_leFn_x3f_2832_;
v___y_2747_ = v___y_2830_;
v___y_2748_ = v___y_2831_;
v_ltFn_x3f_2749_ = v___x_2850_;
v___y_2750_ = v___y_2833_;
v___y_2751_ = v___y_2834_;
v___y_2752_ = v___y_2835_;
v___y_2753_ = v___y_2836_;
v___y_2754_ = v___y_2837_;
v___y_2755_ = v___y_2838_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2840_;
v___y_2758_ = v___y_2841_;
v___y_2759_ = v___y_2842_;
goto v___jp_2725_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref_known(v_a_2649_, 1);
lean_dec(v_leFn_x3f_2832_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v_a_2651_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2852_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2847_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2847_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_dec(v___y_2815_);
lean_del_object(v___x_2642_);
lean_inc(v___y_2818_);
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
v___y_2730_ = v___y_2813_;
v___y_2731_ = v___y_2814_;
v___y_2732_ = v___y_2816_;
v___y_2733_ = v___y_2817_;
v___y_2734_ = v___y_2818_;
v___y_2735_ = v___y_2819_;
v___y_2736_ = v___y_2820_;
v___y_2737_ = v___y_2821_;
v___y_2738_ = v___y_2822_;
v___y_2739_ = v___y_2823_;
v___y_2740_ = v___y_2824_;
v___y_2741_ = v___y_2825_;
v___y_2742_ = v___y_2827_;
v___y_2743_ = v___y_2826_;
v___y_2744_ = v___y_2829_;
v___y_2745_ = v___y_2828_;
v___y_2746_ = v_leFn_x3f_2832_;
v___y_2747_ = v___y_2830_;
v___y_2748_ = v___y_2831_;
v_ltFn_x3f_2749_ = v___y_2818_;
v___y_2750_ = v___y_2833_;
v___y_2751_ = v___y_2834_;
v___y_2752_ = v___y_2835_;
v___y_2753_ = v___y_2836_;
v___y_2754_ = v___y_2837_;
v___y_2755_ = v___y_2838_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2840_;
v___y_2758_ = v___y_2841_;
v___y_2759_ = v___y_2842_;
goto v___jp_2725_;
}
}
v___jp_2860_:
{
lean_object* v___x_2893_; 
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2635_, v_type_2552_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2895_, v_val_2635_, v_type_2552_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_n(v_a_2897_, 2);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2865_);
v___x_2899_ = l_Lean_mkConst(v___x_2898_, v___y_2865_);
lean_inc_ref(v_type_2552_);
v___x_2900_ = l_Lean_mkAppB(v___x_2899_, v_type_2552_, v_a_2897_);
v___x_2901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2900_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2865_);
v___x_2904_ = l_Lean_mkConst(v___x_2903_, v___y_2865_);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2552_);
v___x_2907_ = l_Lean_mkAppB(v___x_2904_, v_type_2552_, v___x_2906_);
v___x_2908_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2907_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_3130_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_3130_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_3130_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
if (lean_obj_tag(v_a_2909_) == 1)
{
lean_object* v_val_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_2911_);
v_val_2913_ = lean_ctor_get(v_a_2909_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_a_2909_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_2915_ = v_a_2909_;
v_isShared_2916_ = v_isSharedCheck_3125_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_val_2913_);
lean_dec(v_a_2909_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3125_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2865_);
v___x_2918_ = l_Lean_mkConst(v___x_2917_, v___y_2865_);
lean_inc_ref(v_type_2552_);
v___x_2919_ = l_Lean_mkApp3(v___x_2918_, v_type_2552_, v___x_2906_, v_val_2913_);
v___x_2920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2919_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_n(v_a_2921_, 2);
lean_dec_ref_known(v___x_2920_, 1);
lean_inc(v_a_2902_);
v___x_2922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2902_, v_a_2921_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2923_, v_val_2635_, v_type_2552_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc_n(v_a_2925_, 2);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2863_);
v___x_2927_ = l_Lean_mkConst(v___x_2926_, v___y_2863_);
lean_inc_ref_n(v_type_2552_, 3);
v___x_2928_ = l_Lean_mkApp4(v___x_2927_, v_type_2552_, v_type_2552_, v_type_2552_, v_a_2925_);
v___x_2929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2928_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2931_, v_val_2635_, v_type_2552_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_n(v_a_2933_, 2);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2865_);
v___x_2935_ = l_Lean_mkConst(v___x_2934_, v___y_2865_);
lean_inc_ref(v_type_2552_);
v___x_2936_ = l_Lean_mkAppB(v___x_2935_, v_type_2552_, v_a_2933_);
v___x_2937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2936_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2635_, v_type_2552_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_n(v_a_2940_, 2);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___y_2880_);
v___x_2944_ = l_Lean_mkConst(v___x_2941_, v___x_2943_);
v___x_2945_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2552_, 2);
lean_inc_ref(v___x_2944_);
v___x_2946_ = l_Lean_mkApp4(v___x_2944_, v___x_2945_, v_type_2552_, v_type_2552_, v_a_2940_);
v___x_2947_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2946_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2635_, v_type_2552_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc_n(v_a_2950_, 2);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2552_, 2);
v___x_2952_ = l_Lean_mkApp4(v___x_2944_, v___x_2951_, v_type_2552_, v_type_2552_, v_a_2950_);
v___x_2953_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2952_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_2956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2957_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___x_2955_, v___x_2956_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc_ref(v___y_2870_);
v___x_2958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2897_, v___y_2870_, v___x_2957_, v_val_2635_, v_type_2552_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2960_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___x_2955_, v___x_2959_);
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_2962_ = lean_box(0);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2872_, v___y_2870_, v___x_2960_, v___x_2961_, v_val_2635_, v_type_2552_, v___x_2962_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec_ref_known(v___x_2963_, 1);
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2868_);
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2965_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___y_2868_, v___x_2964_);
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc_ref(v___y_2879_);
v___x_2967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2925_, v___y_2879_, v___x_2965_, v___x_2966_, v_val_2635_, v_type_2552_, v___x_2962_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2868_);
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2969_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___y_2868_, v___x_2968_);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
v___x_2970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2933_, v___y_2879_, v___x_2969_, v_val_2635_, v_type_2552_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec_ref_known(v___x_2970_, 1);
v___x_2971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2862_);
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2972_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___y_2862_, v___x_2971_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_2974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc_ref(v___y_2866_);
v___x_2975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2940_, v___y_2866_, v___x_2972_, v___x_2973_, v_val_2635_, v_type_2552_, v___x_2974_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref_known(v___x_2975_, 1);
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2862_);
lean_inc_ref(v___y_2876_);
lean_inc_ref(v___y_2873_);
v___x_2977_ = l_Lean_Name_mkStr4(v___y_2873_, v___y_2876_, v___y_2862_, v___x_2976_);
v___x_2978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2552_);
lean_inc(v_val_2635_);
lean_inc_ref(v___y_2866_);
v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2950_, v___y_2866_, v___x_2977_, v___x_2973_, v_val_2635_, v_type_2552_, v___x_2978_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_dec_ref_known(v___x_2979_, 1);
if (lean_obj_tag(v_a_2646_) == 1)
{
lean_object* v_val_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v_val_2980_ = lean_ctor_get(v_a_2646_, 0);
v___x_2981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2865_);
v___x_2982_ = l_Lean_mkConst(v___x_2981_, v___y_2865_);
lean_inc(v_val_2980_);
lean_inc_ref(v_type_2552_);
v___x_2983_ = l_Lean_mkAppB(v___x_2982_, v_type_2552_, v_val_2980_);
v___x_2984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2983_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v_a_2985_);
v___x_2987_ = v___x_2915_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
v___y_2809_ = v_a_2954_;
v___y_2810_ = v_a_2948_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2863_;
v___y_2813_ = v___y_2864_;
v___y_2814_ = v_charInst_x3f_2882_;
v___y_2815_ = v___y_2865_;
v___y_2816_ = v___y_2866_;
v___y_2817_ = v___y_2867_;
v___y_2818_ = v___x_2962_;
v___y_2819_ = v_a_2894_;
v___y_2820_ = v___y_2869_;
v___y_2821_ = v___y_2871_;
v___y_2822_ = v___y_2874_;
v___y_2823_ = v___y_2875_;
v___y_2824_ = v___x_2905_;
v___y_2825_ = v___y_2877_;
v___y_2826_ = v_a_2930_;
v___y_2827_ = v___y_2878_;
v___y_2828_ = v_a_2902_;
v___y_2829_ = v_a_2921_;
v___y_2830_ = v_a_2938_;
v___y_2831_ = v___y_2881_;
v_leFn_x3f_2832_ = v___x_2987_;
v___y_2833_ = v___y_2883_;
v___y_2834_ = v___y_2884_;
v___y_2835_ = v___y_2885_;
v___y_2836_ = v___y_2886_;
v___y_2837_ = v___y_2887_;
v___y_2838_ = v___y_2888_;
v___y_2839_ = v___y_2889_;
v___y_2840_ = v___y_2890_;
v___y_2841_ = v___y_2891_;
v___y_2842_ = v___y_2892_;
goto v___jp_2808_;
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref_known(v_a_2646_, 1);
lean_dec(v_a_2954_);
lean_dec(v_a_2948_);
lean_dec(v_a_2938_);
lean_dec(v_a_2930_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2989_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2984_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
else
{
lean_del_object(v___x_2915_);
v___y_2809_ = v_a_2954_;
v___y_2810_ = v_a_2948_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2863_;
v___y_2813_ = v___y_2864_;
v___y_2814_ = v_charInst_x3f_2882_;
v___y_2815_ = v___y_2865_;
v___y_2816_ = v___y_2866_;
v___y_2817_ = v___y_2867_;
v___y_2818_ = v___x_2962_;
v___y_2819_ = v_a_2894_;
v___y_2820_ = v___y_2869_;
v___y_2821_ = v___y_2871_;
v___y_2822_ = v___y_2874_;
v___y_2823_ = v___y_2875_;
v___y_2824_ = v___x_2905_;
v___y_2825_ = v___y_2877_;
v___y_2826_ = v_a_2930_;
v___y_2827_ = v___y_2878_;
v___y_2828_ = v_a_2902_;
v___y_2829_ = v_a_2921_;
v___y_2830_ = v_a_2938_;
v___y_2831_ = v___y_2881_;
v_leFn_x3f_2832_ = v___x_2962_;
v___y_2833_ = v___y_2883_;
v___y_2834_ = v___y_2884_;
v___y_2835_ = v___y_2885_;
v___y_2836_ = v___y_2886_;
v___y_2837_ = v___y_2887_;
v___y_2838_ = v___y_2888_;
v___y_2839_ = v___y_2889_;
v___y_2840_ = v___y_2890_;
v___y_2841_ = v___y_2891_;
v___y_2842_ = v___y_2892_;
goto v___jp_2808_;
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2948_);
lean_dec(v_a_2938_);
lean_dec(v_a_2930_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_2997_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2979_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2979_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2938_);
lean_dec(v_a_2930_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3005_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2975_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2975_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2930_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3013_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2970_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2970_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3021_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2967_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2967_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v___y_2871_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3029_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2963_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2963_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_2954_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3037_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2958_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2958_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3045_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2953_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2953_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_a_2948_);
lean_dec_ref(v___x_2944_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3053_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2949_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2949_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
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
lean_dec_ref(v___x_2944_);
lean_dec(v_a_2940_);
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3061_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2947_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2947_);
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
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_2938_);
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3069_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2939_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2939_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_a_2933_);
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3077_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2937_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2937_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_2930_);
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3085_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_2932_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_2932_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3093_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_2929_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_2929_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3101_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_2924_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_2924_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v_a_2921_);
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3109_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2922_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2922_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_del_object(v___x_2915_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3117_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_2920_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_2920_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec(v_a_2909_);
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v___x_3126_ = lean_box(0);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_3126_);
v___x_3128_ = v___x_2911_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_a_2902_);
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3131_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_2908_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_2908_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_a_2897_);
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3139_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_2901_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_2901_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_2894_);
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3147_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_2896_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_2896_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_charInst_x3f_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2861_);
lean_dec(v_a_2651_);
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3155_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_2893_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_2893_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v_a_2649_);
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3518_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_2650_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_2650_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_2646_);
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3526_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_2648_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_2648_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_del_object(v___x_2642_);
lean_dec(v_a_2640_);
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
v_a_3534_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_2645_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_2645_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
else
{
lean_del_object(v___x_2637_);
lean_dec(v_val_2635_);
lean_dec_ref(v_type_2552_);
return v___x_2639_;
}
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec(v_a_2631_);
lean_dec_ref(v_type_2552_);
v___x_3544_ = lean_box(0);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_3544_);
v___x_3546_ = v___x_2633_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_type_2552_);
v_a_3549_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_2630_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_2630_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2565_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
v___jp_2568_:
{
if (lean_obj_tag(v___y_2570_) == 0)
{
lean_dec_ref_known(v___y_2570_, 1);
v___y_2565_ = v___y_2569_;
goto v___jp_2564_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v___y_2569_);
v_a_2571_ = lean_ctor_get(v___y_2570_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___y_2570_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___y_2570_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___y_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
v___jp_2579_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2581_, v___y_2586_, v___y_2587_, v___y_2591_, v___y_2588_, v___y_2584_, v___y_2589_, v___y_2580_, v___y_2582_, v___y_2583_, v___y_2590_, v___y_2592_, v___y_2585_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2594_, v___y_2587_, v___y_2591_);
v___y_2569_ = v___y_2587_;
v___y_2570_ = v___x_2595_;
goto v___jp_2568_;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v___y_2587_);
v_a_2596_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2593_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2593_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2606_, v___y_2611_, v___y_2612_, v___y_2616_, v___y_2613_, v___y_2609_, v___y_2614_, v___y_2605_, v___y_2607_, v___y_2608_, v___y_2615_, v___y_2617_, v___y_2610_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_n(v_a_2619_, 2);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2619_, v___y_2612_, v___y_2616_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2620_, 1);
v___x_2621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2619_, v___y_2612_, v___y_2616_);
v___y_2569_ = v___y_2612_;
v___y_2570_ = v___x_2621_;
goto v___jp_2568_;
}
else
{
lean_dec(v_a_2619_);
v___y_2569_ = v___y_2612_;
v___y_2570_ = v___x_2620_;
goto v___jp_2568_;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v___y_2612_);
v_a_2622_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2618_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2618_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec(v_a_3558_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3571_, v_x_3572_, v_x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3575_, lean_object* v_x_3576_, size_t v_x_3577_, size_t v_x_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3576_, v_x_3577_, v_x_3578_, v_x_3579_, v_x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
size_t v_x_529251__boxed_3588_; size_t v_x_529252__boxed_3589_; lean_object* v_res_3590_; 
v_x_529251__boxed_3588_ = lean_unbox_usize(v_x_3584_);
lean_dec(v_x_3584_);
v_x_529252__boxed_3589_ = lean_unbox_usize(v_x_3585_);
lean_dec(v_x_3585_);
v_res_3590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3582_, v_x_3583_, v_x_529251__boxed_3588_, v_x_529252__boxed_3589_, v_x_3586_, v_x_3587_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3591_, lean_object* v_n_3592_, lean_object* v_k_3593_, lean_object* v_v_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3592_, v_k_3593_, v_v_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3596_, size_t v_depth_3597_, lean_object* v_keys_3598_, lean_object* v_vals_3599_, lean_object* v_heq_3600_, lean_object* v_i_3601_, lean_object* v_entries_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3597_, v_keys_3598_, v_vals_3599_, v_i_3601_, v_entries_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3604_, lean_object* v_depth_3605_, lean_object* v_keys_3606_, lean_object* v_vals_3607_, lean_object* v_heq_3608_, lean_object* v_i_3609_, lean_object* v_entries_3610_){
_start:
{
size_t v_depth_boxed_3611_; lean_object* v_res_3612_; 
v_depth_boxed_3611_ = lean_unbox_usize(v_depth_3605_);
lean_dec(v_depth_3605_);
v_res_3612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3604_, v_depth_boxed_3611_, v_keys_3606_, v_vals_3607_, v_heq_3608_, v_i_3609_, v_entries_3610_);
lean_dec_ref(v_vals_3607_);
lean_dec_ref(v_keys_3606_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3614_, v_x_3615_, v_x_3616_, v_x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3619_, lean_object* v_base_3620_, lean_object* v_natModuleInst_3621_, lean_object* v_declName_3622_, lean_object* v_le_3623_, lean_object* v_mid_3624_, lean_object* v_ord_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3626_ = lean_box(0);
v___x_3627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_val_3619_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_mkConst(v_declName_3622_, v___x_3627_);
v___x_3629_ = l_Lean_mkApp5(v___x_3628_, v_base_3620_, v_natModuleInst_3621_, v_le_3623_, v_mid_3624_, v_ord_3625_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3729_, lean_object* v_base_3730_, lean_object* v_natModuleInst_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___x_3743_; 
lean_inc_ref(v_base_3730_);
v___x_3743_ = l_Lean_Meta_getDecLevel_x3f(v_base_3730_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_4481_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_4481_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_4481_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
if (lean_obj_tag(v_a_3744_) == 1)
{
lean_object* v_val_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_3746_);
v_val_3748_ = lean_ctor_get(v_a_3744_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_3750_ = v_a_3744_;
v_isShared_3751_ = v_isSharedCheck_4476_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_val_3748_);
lean_dec(v_a_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_4476_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v_a_3772_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v_a_3844_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___x_4062_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v_noNatDivInstQ_x3f_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v_isLinearInstQ_x3f_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___x_4317_; 
v___x_4062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4062_, v_val_3748_, v_base_3730_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc_n(v_a_4318_, 2);
lean_dec_ref_known(v___x_4317_, 1);
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4319_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_3748_, v_base_3730_, v_a_4318_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v_fst_4328_; lean_object* v_snd_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v_orderedAddInst_x3f_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
if (lean_obj_tag(v_a_4318_) == 1)
{
if (lean_obj_tag(v_a_4320_) == 1)
{
lean_object* v_val_4432_; lean_object* v_val_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_val_4432_ = lean_ctor_get(v_a_4318_, 0);
v_val_4433_ = lean_ctor_get(v_a_4320_, 0);
v___x_4434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4434_, v_val_3748_, v_base_3730_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4438_ = lean_box(0);
lean_inc(v_val_3748_);
v___x_4439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4439_, 0, v_val_3748_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = l_Lean_mkConst(v___x_4437_, v___x_4439_);
lean_inc(v_val_4433_);
lean_inc(v_val_4432_);
lean_inc_ref(v_base_3730_);
v___x_4441_ = l_Lean_mkApp4(v___x_4440_, v_base_3730_, v_a_4436_, v_val_4432_, v_val_4433_);
v___x_4442_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4441_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v_orderedAddInst_x3f_4373_ = v_a_4443_;
v___y_4374_ = v_a_3732_;
v___y_4375_ = v_a_3733_;
v___y_4376_ = v_a_3734_;
v___y_4377_ = v_a_3735_;
v___y_4378_ = v_a_3736_;
v___y_4379_ = v_a_3737_;
v___y_4380_ = v_a_3738_;
v___y_4381_ = v_a_3739_;
v___y_4382_ = v_a_3740_;
v___y_4383_ = v_a_3741_;
goto v___jp_4372_;
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref_known(v_a_4320_, 1);
lean_dec_ref_known(v_a_4318_, 1);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4444_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4442_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4442_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref_known(v_a_4320_, 1);
lean_dec_ref_known(v_a_4318_, 1);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4452_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4435_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4435_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
v___y_4421_ = v_a_3732_;
v___y_4422_ = v_a_3733_;
v___y_4423_ = v_a_3734_;
v___y_4424_ = v_a_3735_;
v___y_4425_ = v_a_3736_;
v___y_4426_ = v_a_3737_;
v___y_4427_ = v_a_3738_;
v___y_4428_ = v_a_3739_;
v___y_4429_ = v_a_3740_;
v___y_4430_ = v_a_3741_;
goto v___jp_4420_;
}
}
else
{
v___y_4421_ = v_a_3732_;
v___y_4422_ = v_a_3733_;
v___y_4423_ = v_a_3734_;
v___y_4424_ = v_a_3735_;
v___y_4425_ = v_a_3736_;
v___y_4426_ = v_a_3737_;
v___y_4427_ = v_a_3738_;
v___y_4428_ = v_a_3739_;
v___y_4429_ = v_a_3740_;
v___y_4430_ = v_a_3741_;
goto v___jp_4420_;
}
v___jp_4321_:
{
lean_object* v___x_4339_; 
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4339_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_3748_, v_base_3730_, v_a_4318_, v___y_4327_, v___y_4336_, v___y_4333_, v___y_4337_, v___y_4324_, v___y_4323_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4339_, 1);
if (lean_obj_tag(v_a_4340_) == 0)
{
lean_dec_ref(v_snd_4329_);
lean_dec_ref(v_fst_4328_);
v___y_4244_ = v___y_4322_;
v___y_4245_ = v___y_4330_;
v___y_4246_ = v___y_4331_;
v___y_4247_ = v___y_4334_;
v___y_4248_ = v___y_4338_;
v_isLinearInstQ_x3f_4249_ = v_a_4340_;
v___y_4250_ = v___y_4335_;
v___y_4251_ = v___y_4325_;
v___y_4252_ = v___y_4326_;
v___y_4253_ = v___y_4332_;
v___y_4254_ = v___y_4327_;
v___y_4255_ = v___y_4336_;
v___y_4256_ = v___y_4333_;
v___y_4257_ = v___y_4337_;
v___y_4258_ = v___y_4324_;
v___y_4259_ = v___y_4323_;
goto v___jp_4243_;
}
else
{
lean_object* v_val_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4350_; 
v_val_4341_ = lean_ctor_get(v_a_4340_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_a_4340_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4343_ = v_a_4340_;
v_isShared_4344_ = v_isSharedCheck_4350_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_val_4341_);
lean_dec(v_a_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4350_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3731_);
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3748_, v_base_3730_, v_natModuleInst_3731_, v___x_4345_, v_fst_4328_, v_val_4341_, v_snd_4329_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v___x_4346_);
v___x_4348_ = v___x_4343_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
v___y_4244_ = v___y_4322_;
v___y_4245_ = v___y_4330_;
v___y_4246_ = v___y_4331_;
v___y_4247_ = v___y_4334_;
v___y_4248_ = v___y_4338_;
v_isLinearInstQ_x3f_4249_ = v___x_4348_;
v___y_4250_ = v___y_4335_;
v___y_4251_ = v___y_4325_;
v___y_4252_ = v___y_4326_;
v___y_4253_ = v___y_4332_;
v___y_4254_ = v___y_4327_;
v___y_4255_ = v___y_4336_;
v___y_4256_ = v___y_4333_;
v___y_4257_ = v___y_4337_;
v___y_4258_ = v___y_4324_;
v___y_4259_ = v___y_4323_;
goto v___jp_4243_;
}
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v___y_4338_);
lean_dec(v___y_4334_);
lean_dec(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v_snd_4329_);
lean_dec_ref(v_fst_4328_);
lean_dec(v___y_4322_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4351_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4339_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4339_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
v___jp_4359_:
{
lean_object* v___x_4371_; 
v___x_4371_ = lean_box(0);
v___y_4244_ = v___x_4371_;
v___y_4245_ = v___x_4371_;
v___y_4246_ = v___x_4371_;
v___y_4247_ = v___x_4371_;
v___y_4248_ = v___x_4371_;
v_isLinearInstQ_x3f_4249_ = v___x_4371_;
v___y_4250_ = v___y_4362_;
v___y_4251_ = v___y_4367_;
v___y_4252_ = v___y_4368_;
v___y_4253_ = v___y_4360_;
v___y_4254_ = v___y_4369_;
v___y_4255_ = v___y_4363_;
v___y_4256_ = v___y_4361_;
v___y_4257_ = v___y_4364_;
v___y_4258_ = v___y_4366_;
v___y_4259_ = v___y_4365_;
goto v___jp_4243_;
}
v___jp_4372_:
{
if (lean_obj_tag(v_a_4318_) == 0)
{
lean_object* v___x_4384_; 
lean_dec(v_orderedAddInst_x3f_4373_);
lean_dec(v_a_4320_);
v___x_4384_ = lean_box(0);
v___y_4360_ = v___y_4377_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4374_;
v___y_4363_ = v___y_4379_;
v___y_4364_ = v___y_4381_;
v___y_4365_ = v___y_4383_;
v___y_4366_ = v___y_4382_;
v___y_4367_ = v___y_4375_;
v___y_4368_ = v___y_4376_;
v___y_4369_ = v___y_4378_;
v___y_4370_ = v___x_4384_;
goto v___jp_4359_;
}
else
{
if (lean_obj_tag(v_a_4320_) == 0)
{
lean_object* v___x_4385_; 
lean_dec_ref_known(v_a_4318_, 1);
lean_dec(v_orderedAddInst_x3f_4373_);
v___x_4385_ = lean_box(0);
v___y_4360_ = v___y_4377_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4374_;
v___y_4363_ = v___y_4379_;
v___y_4364_ = v___y_4381_;
v___y_4365_ = v___y_4383_;
v___y_4366_ = v___y_4382_;
v___y_4367_ = v___y_4375_;
v___y_4368_ = v___y_4376_;
v___y_4369_ = v___y_4378_;
v___y_4370_ = v___x_4385_;
goto v___jp_4359_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4373_) == 0)
{
lean_object* v___x_4386_; 
lean_dec_ref_known(v_a_4320_, 1);
lean_dec_ref_known(v_a_4318_, 1);
v___x_4386_ = lean_box(0);
v___y_4360_ = v___y_4377_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4374_;
v___y_4363_ = v___y_4379_;
v___y_4364_ = v___y_4381_;
v___y_4365_ = v___y_4383_;
v___y_4366_ = v___y_4382_;
v___y_4367_ = v___y_4375_;
v___y_4368_ = v___y_4376_;
v___y_4369_ = v___y_4378_;
v___y_4370_ = v___x_4386_;
goto v___jp_4359_;
}
else
{
lean_object* v_val_4387_; lean_object* v_val_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4419_; 
v_val_4387_ = lean_ctor_get(v_a_4318_, 0);
v_val_4388_ = lean_ctor_get(v_a_4320_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_a_4320_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4390_ = v_a_4320_;
v_isShared_4391_ = v_isSharedCheck_4419_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_val_4388_);
lean_dec(v_a_4320_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4419_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v_val_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4418_; 
v_val_4392_ = lean_ctor_get(v_orderedAddInst_x3f_4373_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_orderedAddInst_x3f_4373_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4394_ = v_orderedAddInst_x3f_4373_;
v_isShared_4395_ = v_isSharedCheck_4418_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_val_4392_);
lean_dec(v_orderedAddInst_x3f_4373_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4418_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4392_);
lean_inc(v_val_4388_);
lean_inc(v_val_4387_);
lean_inc_ref(v_natModuleInst_3731_);
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4397_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3748_, v_base_3730_, v_natModuleInst_3731_, v___x_4396_, v_val_4387_, v_val_4388_, v_val_4392_);
lean_inc_ref(v___x_4397_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4397_);
v___x_4399_ = v___x_4394_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4392_);
lean_inc(v_val_4388_);
lean_inc(v_val_4387_);
lean_inc_ref(v_natModuleInst_3731_);
lean_inc_ref(v_base_3730_);
lean_inc(v_val_3748_);
v___x_4401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3748_, v_base_3730_, v_natModuleInst_3731_, v___x_4400_, v_val_4387_, v_val_4388_, v_val_4392_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4401_);
v___x_4403_ = v___x_4390_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4392_, 2);
lean_inc(v_val_4388_);
lean_inc_n(v_val_4387_, 3);
lean_inc_ref_n(v_natModuleInst_3731_, 2);
lean_inc_ref_n(v_base_3730_, 2);
lean_inc_n(v_val_3748_, 3);
v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3748_, v_base_3730_, v_natModuleInst_3731_, v___x_4404_, v_val_4387_, v_val_4388_, v_val_4392_);
v___x_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
v___x_4407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3748_, v_base_3730_, v_natModuleInst_3731_, v___x_4407_, v_val_4387_, v_val_4388_, v_val_4392_);
v___x_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
v___x_4410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4411_ = lean_box(0);
v___x_4412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4412_, 0, v_val_3748_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = l_Lean_mkConst(v___x_4410_, v___x_4412_);
lean_inc_ref(v_type_3729_);
v___x_4414_ = l_Lean_mkAppB(v___x_4413_, v_type_3729_, v___x_4397_);
v___x_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
v___y_4322_ = v___x_4409_;
v___y_4323_ = v___y_4383_;
v___y_4324_ = v___y_4382_;
v___y_4325_ = v___y_4375_;
v___y_4326_ = v___y_4376_;
v___y_4327_ = v___y_4378_;
v_fst_4328_ = v_val_4387_;
v_snd_4329_ = v_val_4392_;
v___y_4330_ = v___x_4406_;
v___y_4331_ = v___x_4403_;
v___y_4332_ = v___y_4377_;
v___y_4333_ = v___y_4380_;
v___y_4334_ = v___x_4399_;
v___y_4335_ = v___y_4374_;
v___y_4336_ = v___y_4379_;
v___y_4337_ = v___y_4381_;
v___y_4338_ = v___x_4415_;
goto v___jp_4321_;
}
}
}
}
}
}
}
}
v___jp_4420_:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_box(0);
v_orderedAddInst_x3f_4373_ = v___x_4431_;
v___y_4374_ = v___y_4421_;
v___y_4375_ = v___y_4422_;
v___y_4376_ = v___y_4423_;
v___y_4377_ = v___y_4424_;
v___y_4378_ = v___y_4425_;
v___y_4379_ = v___y_4426_;
v___y_4380_ = v___y_4427_;
v___y_4381_ = v___y_4428_;
v___y_4382_ = v___y_4429_;
v___y_4383_ = v___y_4430_;
goto v___jp_4372_;
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_a_4318_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4460_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4319_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4319_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4468_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4317_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4317_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
v___jp_3752_:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3760_, v___y_3757_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v_structs_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v_structs_3775_ = lean_ctor_get(v_a_3774_, 0);
lean_inc_ref(v_structs_3775_);
lean_dec(v_a_3774_);
v___x_3776_ = lean_array_get_size(v_structs_3775_);
lean_dec_ref(v_structs_3775_);
v___x_3777_ = lean_box(0);
lean_inc_ref(v___y_3753_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___y_3753_);
v___x_3779_ = v___x_3750_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___y_3753_);
v___x_3779_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; size_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___f_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_inc_ref(v___y_3766_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___y_3766_);
v___x_3781_ = lean_unsigned_to_nat(32u);
v___x_3782_ = lean_mk_empty_array_with_capacity(v___x_3781_);
v___x_3783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3784_ = ((size_t)5ULL);
lean_inc(v___y_3769_);
v___x_3785_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3782_);
lean_ctor_set(v___x_3785_, 2, v___y_3769_);
lean_ctor_set(v___x_3785_, 3, v___y_3769_);
lean_ctor_set_usize(v___x_3785_, 4, v___x_3784_);
v___x_3786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3787_ = 0;
v___x_3788_ = lean_box(0);
lean_inc_ref_n(v___x_3785_, 7);
v___x_3789_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3789_, 0, v___x_3776_);
lean_ctor_set(v___x_3789_, 1, v___x_3777_);
lean_ctor_set(v___x_3789_, 2, v_type_3729_);
lean_ctor_set(v___x_3789_, 3, v_val_3748_);
lean_ctor_set(v___x_3789_, 4, v___y_3765_);
lean_ctor_set(v___x_3789_, 5, v___y_3770_);
lean_ctor_set(v___x_3789_, 6, v___y_3768_);
lean_ctor_set(v___x_3789_, 7, v___y_3764_);
lean_ctor_set(v___x_3789_, 8, v___y_3767_);
lean_ctor_set(v___x_3789_, 9, v___y_3758_);
lean_ctor_set(v___x_3789_, 10, v___y_3754_);
lean_ctor_set(v___x_3789_, 11, v___y_3755_);
lean_ctor_set(v___x_3789_, 12, v___x_3777_);
lean_ctor_set(v___x_3789_, 13, v___x_3777_);
lean_ctor_set(v___x_3789_, 14, v___x_3777_);
lean_ctor_set(v___x_3789_, 15, v___x_3777_);
lean_ctor_set(v___x_3789_, 16, v___x_3777_);
lean_ctor_set(v___x_3789_, 17, v___y_3761_);
lean_ctor_set(v___x_3789_, 18, v___y_3759_);
lean_ctor_set(v___x_3789_, 19, v___x_3777_);
lean_ctor_set(v___x_3789_, 20, v___y_3756_);
lean_ctor_set(v___x_3789_, 21, v_a_3772_);
lean_ctor_set(v___x_3789_, 22, v___y_3763_);
lean_ctor_set(v___x_3789_, 23, v___y_3753_);
lean_ctor_set(v___x_3789_, 24, v___y_3766_);
lean_ctor_set(v___x_3789_, 25, v___x_3779_);
lean_ctor_set(v___x_3789_, 26, v___x_3780_);
lean_ctor_set(v___x_3789_, 27, v___x_3777_);
lean_ctor_set(v___x_3789_, 28, v___y_3762_);
lean_ctor_set(v___x_3789_, 29, v___y_3771_);
lean_ctor_set(v___x_3789_, 30, v___x_3785_);
lean_ctor_set(v___x_3789_, 31, v___x_3786_);
lean_ctor_set(v___x_3789_, 32, v___x_3785_);
lean_ctor_set(v___x_3789_, 33, v___x_3785_);
lean_ctor_set(v___x_3789_, 34, v___x_3785_);
lean_ctor_set(v___x_3789_, 35, v___x_3785_);
lean_ctor_set(v___x_3789_, 36, v___x_3777_);
lean_ctor_set(v___x_3789_, 37, v___x_3786_);
lean_ctor_set(v___x_3789_, 38, v___x_3785_);
lean_ctor_set(v___x_3789_, 39, v___x_3788_);
lean_ctor_set(v___x_3789_, 40, v___x_3785_);
lean_ctor_set(v___x_3789_, 41, v___x_3785_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*42, v___x_3787_);
v___f_3790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_3790_, 0, v___x_3789_);
v___x_3791_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3792_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3791_, v___f_3790_, v___y_3760_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3800_; 
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3801_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3776_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3792_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3792_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec(v_a_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3811_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3773_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3773_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
v___jp_3819_:
{
if (lean_obj_tag(v___y_3838_) == 0)
{
lean_dec(v___y_3825_);
v___y_3753_ = v___y_3820_;
v___y_3754_ = v___y_3821_;
v___y_3755_ = v___y_3822_;
v___y_3756_ = v_a_3844_;
v___y_3757_ = v___y_3823_;
v___y_3758_ = v___y_3824_;
v___y_3759_ = v___y_3826_;
v___y_3760_ = v___y_3827_;
v___y_3761_ = v___y_3828_;
v___y_3762_ = v___y_3830_;
v___y_3763_ = v___y_3833_;
v___y_3764_ = v___y_3834_;
v___y_3765_ = v___y_3835_;
v___y_3766_ = v___y_3837_;
v___y_3767_ = v___y_3836_;
v___y_3768_ = v___y_3838_;
v___y_3769_ = v___y_3840_;
v___y_3770_ = v___y_3841_;
v___y_3771_ = v___y_3843_;
v_a_3772_ = v___y_3838_;
goto v___jp_3752_;
}
else
{
lean_object* v_val_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_val_3845_ = lean_ctor_get(v___y_3838_, 0);
v___x_3846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3847_ = l_Lean_mkConst(v___x_3846_, v___y_3825_);
lean_inc(v_val_3845_);
lean_inc_ref(v_type_3729_);
v___x_3848_ = l_Lean_mkAppB(v___x_3847_, v_type_3729_, v_val_3845_);
v___x_3849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3848_, v___y_3831_, v___y_3832_, v___y_3829_, v___y_3839_, v___y_3823_, v___y_3842_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_a_3850_);
v___y_3753_ = v___y_3820_;
v___y_3754_ = v___y_3821_;
v___y_3755_ = v___y_3822_;
v___y_3756_ = v_a_3844_;
v___y_3757_ = v___y_3823_;
v___y_3758_ = v___y_3824_;
v___y_3759_ = v___y_3826_;
v___y_3760_ = v___y_3827_;
v___y_3761_ = v___y_3828_;
v___y_3762_ = v___y_3830_;
v___y_3763_ = v___y_3833_;
v___y_3764_ = v___y_3834_;
v___y_3765_ = v___y_3835_;
v___y_3766_ = v___y_3837_;
v___y_3767_ = v___y_3836_;
v___y_3768_ = v___y_3838_;
v___y_3769_ = v___y_3840_;
v___y_3770_ = v___y_3841_;
v___y_3771_ = v___y_3843_;
v_a_3772_ = v___x_3851_;
goto v___jp_3752_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref_known(v___y_3838_, 1);
lean_dec(v_a_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3828_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3824_);
lean_dec(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3852_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3849_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3849_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
v___jp_3860_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3875_);
v___x_3900_ = l_Lean_Name_mkStr2(v___y_3875_, v___x_3899_);
lean_inc(v___y_3865_);
v___x_3901_ = l_Lean_mkConst(v___x_3900_, v___y_3865_);
lean_inc_ref(v_type_3729_);
v___x_3902_ = l_Lean_mkAppB(v___x_3901_, v_type_3729_, v___y_3871_);
v___x_3903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3902_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3884_);
v___x_3906_ = l_Lean_Name_mkStr2(v___y_3884_, v___x_3905_);
lean_inc(v___y_3865_);
v___x_3907_ = l_Lean_mkConst(v___x_3906_, v___y_3865_);
lean_inc_ref(v_type_3729_);
v___x_3908_ = l_Lean_mkApp3(v___x_3907_, v_type_3729_, v___y_3881_, v___y_3877_);
v___x_3909_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3908_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3861_);
v___x_3912_ = l_Lean_Name_mkStr2(v___y_3861_, v___x_3911_);
lean_inc(v___y_3873_);
v___x_3913_ = l_Lean_mkConst(v___x_3912_, v___y_3873_);
lean_inc_ref_n(v_type_3729_, 3);
v___x_3914_ = l_Lean_mkApp4(v___x_3913_, v_type_3729_, v_type_3729_, v_type_3729_, v___y_3879_);
v___x_3915_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3914_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3876_);
v___x_3918_ = l_Lean_Name_mkStr2(v___y_3876_, v___x_3917_);
v___x_3919_ = l_Lean_mkConst(v___x_3918_, v___y_3873_);
lean_inc_ref_n(v_type_3729_, 3);
v___x_3920_ = l_Lean_mkApp4(v___x_3919_, v_type_3729_, v_type_3729_, v_type_3729_, v___y_3887_);
v___x_3921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3920_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3869_);
v___x_3924_ = l_Lean_Name_mkStr2(v___y_3869_, v___x_3923_);
lean_inc(v___y_3865_);
v___x_3925_ = l_Lean_mkConst(v___x_3924_, v___y_3865_);
lean_inc_ref(v_type_3729_);
v___x_3926_ = l_Lean_mkAppB(v___x_3925_, v_type_3729_, v___y_3866_);
v___x_3927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3926_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3880_);
v___x_3930_ = l_Lean_Name_mkStr2(v___y_3880_, v___x_3929_);
v___x_3931_ = l_Lean_mkConst(v___x_3930_, v___y_3888_);
lean_inc_ref_n(v_type_3729_, 2);
lean_inc_ref(v___x_3931_);
v___x_3932_ = l_Lean_mkApp4(v___x_3931_, v___y_3882_, v_type_3729_, v_type_3729_, v___y_3886_);
v___x_3933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3932_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
lean_inc_ref_n(v_type_3729_, 2);
v___x_3935_ = l_Lean_mkApp4(v___x_3931_, v___y_3867_, v_type_3729_, v_type_3729_, v___y_3862_);
v___x_3936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3935_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3936_) == 0)
{
if (lean_obj_tag(v___y_3874_) == 0)
{
lean_object* v_a_3937_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v___y_3820_ = v_a_3934_;
v___y_3821_ = v___y_3863_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v___y_3897_;
v___y_3824_ = v___y_3864_;
v___y_3825_ = v___y_3865_;
v___y_3826_ = v_a_3910_;
v___y_3827_ = v___y_3889_;
v___y_3828_ = v_a_3904_;
v___y_3829_ = v___y_3895_;
v___y_3830_ = v_a_3922_;
v___y_3831_ = v___y_3893_;
v___y_3832_ = v___y_3894_;
v___y_3833_ = v_a_3916_;
v___y_3834_ = v___y_3883_;
v___y_3835_ = v___y_3868_;
v___y_3836_ = v___y_3885_;
v___y_3837_ = v_a_3937_;
v___y_3838_ = v___y_3870_;
v___y_3839_ = v___y_3896_;
v___y_3840_ = v___y_3872_;
v___y_3841_ = v___y_3874_;
v___y_3842_ = v___y_3898_;
v___y_3843_ = v_a_3928_;
v_a_3844_ = v___y_3874_;
goto v___jp_3819_;
}
else
{
lean_object* v_a_3938_; lean_object* v_val_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3938_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3936_, 1);
v_val_3939_ = lean_ctor_get(v___y_3874_, 0);
v___x_3940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3865_);
v___x_3941_ = l_Lean_mkConst(v___x_3940_, v___y_3865_);
lean_inc(v_val_3939_);
lean_inc_ref(v_type_3729_);
v___x_3942_ = l_Lean_mkAppB(v___x_3941_, v_type_3729_, v_val_3939_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3942_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_a_3944_);
v___y_3820_ = v_a_3934_;
v___y_3821_ = v___y_3863_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v___y_3897_;
v___y_3824_ = v___y_3864_;
v___y_3825_ = v___y_3865_;
v___y_3826_ = v_a_3910_;
v___y_3827_ = v___y_3889_;
v___y_3828_ = v_a_3904_;
v___y_3829_ = v___y_3895_;
v___y_3830_ = v_a_3922_;
v___y_3831_ = v___y_3893_;
v___y_3832_ = v___y_3894_;
v___y_3833_ = v_a_3916_;
v___y_3834_ = v___y_3883_;
v___y_3835_ = v___y_3868_;
v___y_3836_ = v___y_3885_;
v___y_3837_ = v_a_3938_;
v___y_3838_ = v___y_3870_;
v___y_3839_ = v___y_3896_;
v___y_3840_ = v___y_3872_;
v___y_3841_ = v___y_3874_;
v___y_3842_ = v___y_3898_;
v___y_3843_ = v_a_3928_;
v_a_3844_ = v___x_3945_;
goto v___jp_3819_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref_known(v___y_3874_, 1);
lean_dec(v_a_3938_);
lean_dec(v_a_3934_);
lean_dec(v_a_3928_);
lean_dec(v_a_3922_);
lean_dec(v_a_3916_);
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec(v___y_3878_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3946_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3943_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3943_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_a_3934_);
lean_dec(v_a_3928_);
lean_dec(v_a_3922_);
lean_dec(v_a_3916_);
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3954_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3936_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3936_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v___x_3931_);
lean_dec(v_a_3928_);
lean_dec(v_a_3922_);
lean_dec(v_a_3916_);
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3962_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3933_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3933_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec(v_a_3922_);
lean_dec(v_a_3916_);
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3970_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3927_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3927_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_a_3916_);
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3978_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3921_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3921_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v_a_3910_);
lean_dec(v_a_3904_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3986_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3915_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3915_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec(v_a_3904_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_3994_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3909_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3909_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4002_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3903_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3903_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
v___jp_4010_:
{
if (lean_obj_tag(v___y_4021_) == 1)
{
lean_object* v_val_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_val_4049_ = lean_ctor_get(v___y_4021_, 0);
v___x_4050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_4015_);
v___x_4051_ = l_Lean_mkConst(v___x_4050_, v___y_4015_);
lean_inc_ref(v_type_3729_);
v___x_4052_ = l_Lean_Expr_app___override(v___x_4051_, v_type_3729_);
lean_inc(v_val_4049_);
v___x_4053_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4052_, v_val_4049_, v___y_4044_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_dec_ref_known(v___x_4053_, 1);
v___y_3861_ = v___y_4013_;
v___y_3862_ = v___y_4012_;
v___y_3863_ = v___y_4011_;
v___y_3864_ = v___y_4014_;
v___y_3865_ = v___y_4015_;
v___y_3866_ = v___y_4016_;
v___y_3867_ = v___y_4017_;
v___y_3868_ = v___y_4018_;
v___y_3869_ = v___y_4019_;
v___y_3870_ = v___y_4021_;
v___y_3871_ = v___y_4020_;
v___y_3872_ = v___y_4023_;
v___y_3873_ = v___y_4022_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4026_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4028_;
v___y_3879_ = v___y_4029_;
v___y_3880_ = v___y_4030_;
v___y_3881_ = v___y_4031_;
v___y_3882_ = v___y_4032_;
v___y_3883_ = v___y_4033_;
v___y_3884_ = v___y_4034_;
v___y_3885_ = v___y_4035_;
v___y_3886_ = v___y_4036_;
v___y_3887_ = v___y_4037_;
v___y_3888_ = v___y_4038_;
v___y_3889_ = v___y_4039_;
v___y_3890_ = v___y_4040_;
v___y_3891_ = v___y_4041_;
v___y_3892_ = v___y_4042_;
v___y_3893_ = v___y_4043_;
v___y_3894_ = v___y_4044_;
v___y_3895_ = v___y_4045_;
v___y_3896_ = v___y_4046_;
v___y_3897_ = v___y_4047_;
v___y_3898_ = v___y_4048_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref_known(v___y_4021_, 1);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4020_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
v___y_3861_ = v___y_4013_;
v___y_3862_ = v___y_4012_;
v___y_3863_ = v___y_4011_;
v___y_3864_ = v___y_4014_;
v___y_3865_ = v___y_4015_;
v___y_3866_ = v___y_4016_;
v___y_3867_ = v___y_4017_;
v___y_3868_ = v___y_4018_;
v___y_3869_ = v___y_4019_;
v___y_3870_ = v___y_4021_;
v___y_3871_ = v___y_4020_;
v___y_3872_ = v___y_4023_;
v___y_3873_ = v___y_4022_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4026_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4028_;
v___y_3879_ = v___y_4029_;
v___y_3880_ = v___y_4030_;
v___y_3881_ = v___y_4031_;
v___y_3882_ = v___y_4032_;
v___y_3883_ = v___y_4033_;
v___y_3884_ = v___y_4034_;
v___y_3885_ = v___y_4035_;
v___y_3886_ = v___y_4036_;
v___y_3887_ = v___y_4037_;
v___y_3888_ = v___y_4038_;
v___y_3889_ = v___y_4039_;
v___y_3890_ = v___y_4040_;
v___y_3891_ = v___y_4041_;
v___y_3892_ = v___y_4042_;
v___y_3893_ = v___y_4043_;
v___y_3894_ = v___y_4044_;
v___y_3895_ = v___y_4045_;
v___y_3896_ = v___y_4046_;
v___y_3897_ = v___y_4047_;
v___y_3898_ = v___y_4048_;
goto v___jp_3860_;
}
}
v___jp_4063_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4068_, 14);
v___x_4083_ = l_Lean_mkConst(v___x_4082_, v___y_4068_);
v___x_4084_ = l_Lean_mkAppB(v___x_4083_, v_base_3730_, v_natModuleInst_3731_);
v___x_4085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4086_ = l_Lean_mkConst(v___x_4085_, v___y_4068_);
lean_inc_ref_n(v___x_4084_, 4);
lean_inc_ref_n(v_type_3729_, 14);
v___x_4087_ = l_Lean_mkAppB(v___x_4086_, v_type_3729_, v___x_4084_);
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4089_ = l_Lean_mkConst(v___x_4088_, v___y_4068_);
lean_inc_ref_n(v___x_4087_, 2);
v___x_4090_ = l_Lean_mkAppB(v___x_4089_, v_type_3729_, v___x_4087_);
v___x_4091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4092_ = l_Lean_mkConst(v___x_4091_, v___y_4068_);
lean_inc_ref(v___x_4090_);
v___x_4093_ = l_Lean_mkAppB(v___x_4092_, v_type_3729_, v___x_4090_);
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4096_ = l_Lean_mkConst(v___x_4095_, v___y_4068_);
lean_inc_ref(v___x_4093_);
v___x_4097_ = l_Lean_mkAppB(v___x_4096_, v_type_3729_, v___x_4093_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4099_ = l_Lean_mkConst(v___x_4098_, v___y_4068_);
v___x_4100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4101_ = l_Lean_mkConst(v___x_4100_, v___y_4068_);
v___x_4102_ = l_Lean_mkAppB(v___x_4101_, v_type_3729_, v___x_4090_);
v___x_4103_ = l_Lean_mkAppB(v___x_4099_, v_type_3729_, v___x_4102_);
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4105_ = l_Lean_mkConst(v___x_4104_, v___y_4068_);
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4107_ = l_Lean_mkConst(v___x_4106_, v___y_4068_);
v___x_4108_ = l_Lean_mkAppB(v___x_4107_, v_type_3729_, v___x_4087_);
v___x_4109_ = l_Lean_mkAppB(v___x_4105_, v_type_3729_, v___x_4108_);
v___x_4110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4111_ = l_Lean_mkConst(v___x_4110_, v___y_4068_);
v___x_4112_ = l_Lean_mkAppB(v___x_4111_, v_type_3729_, v___x_4087_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4114_ = lean_unsigned_to_nat(0u);
v___x_4115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v___y_4068_);
v___x_4117_ = l_Lean_mkConst(v___x_4113_, v___x_4116_);
v___x_4118_ = l_Lean_Int_mkType;
v___x_4119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4120_ = l_Lean_mkConst(v___x_4119_, v___y_4068_);
v___x_4121_ = l_Lean_mkAppB(v___x_4120_, v_type_3729_, v___x_4084_);
lean_inc_ref(v___x_4117_);
v___x_4122_ = l_Lean_mkApp3(v___x_4117_, v___x_4118_, v_type_3729_, v___x_4121_);
v___x_4123_ = l_Lean_Nat_mkType;
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4125_ = l_Lean_mkConst(v___x_4124_, v___y_4068_);
v___x_4126_ = l_Lean_mkAppB(v___x_4125_, v_type_3729_, v___x_4084_);
v___x_4127_ = l_Lean_mkApp3(v___x_4117_, v___x_4123_, v_type_3729_, v___x_4126_);
v___x_4128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4129_ = l_Lean_mkConst(v___x_4128_, v___y_4068_);
v___x_4130_ = l_Lean_Expr_app___override(v___x_4129_, v_type_3729_);
v___x_4131_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4130_, v___x_4084_, v___y_4077_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref_known(v___x_4131_, 1);
v___x_4132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4068_);
v___x_4133_ = l_Lean_mkConst(v___x_4132_, v___y_4068_);
lean_inc_ref(v_type_3729_);
v___x_4134_ = l_Lean_Expr_app___override(v___x_4133_, v_type_3729_);
lean_inc_ref(v___x_4093_);
v___x_4135_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4134_, v___x_4093_, v___y_4077_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_dec_ref_known(v___x_4135_, 1);
v___x_4136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4068_);
v___x_4138_ = l_Lean_mkConst(v___x_4137_, v___y_4068_);
v___x_4139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3729_);
v___x_4140_ = l_Lean_mkAppB(v___x_4138_, v_type_3729_, v___x_4139_);
lean_inc_ref(v___x_4097_);
v___x_4141_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4140_, v___x_4097_, v___y_4077_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref_known(v___x_4141_, 1);
v___x_4142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4068_);
lean_inc_n(v_val_3748_, 2);
v___x_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4144_, 0, v_val_3748_);
lean_ctor_set(v___x_4144_, 1, v___y_4068_);
lean_inc_ref(v___x_4144_);
v___x_4145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_val_3748_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
lean_inc_ref(v___x_4145_);
v___x_4146_ = l_Lean_mkConst(v___x_4143_, v___x_4145_);
lean_inc_ref_n(v_type_3729_, 3);
v___x_4147_ = l_Lean_mkApp3(v___x_4146_, v_type_3729_, v_type_3729_, v_type_3729_);
lean_inc_ref(v___x_4103_);
v___x_4148_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4147_, v___x_4103_, v___y_4077_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec_ref_known(v___x_4148_, 1);
v___x_4149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4145_);
v___x_4151_ = l_Lean_mkConst(v___x_4150_, v___x_4145_);
lean_inc_ref_n(v_type_3729_, 3);
v___x_4152_ = l_Lean_mkApp3(v___x_4151_, v_type_3729_, v_type_3729_, v_type_3729_);
lean_inc_ref(v___x_4109_);
v___x_4153_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4152_, v___x_4109_, v___y_4077_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec_ref_known(v___x_4153_, 1);
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4068_);
v___x_4156_ = l_Lean_mkConst(v___x_4155_, v___y_4068_);
lean_inc_ref(v_type_3729_);
v___x_4157_ = l_Lean_Expr_app___override(v___x_4156_, v_type_3729_);
lean_inc_ref(v___x_4112_);
v___x_4158_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4157_, v___x_4112_, v___y_4077_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec_ref_known(v___x_4158_, 1);
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4115_);
lean_ctor_set(v___x_4161_, 1, v___x_4144_);
lean_inc_ref(v___x_4161_);
v___x_4162_ = l_Lean_mkConst(v___x_4160_, v___x_4161_);
lean_inc_ref_n(v_type_3729_, 2);
lean_inc_ref(v___x_4162_);
v___x_4163_ = l_Lean_mkApp3(v___x_4162_, v___x_4118_, v_type_3729_, v_type_3729_);
lean_inc_ref(v___x_4122_);
v___x_4164_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4163_, v___x_4122_, v___y_4077_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref_known(v___x_4164_, 1);
lean_inc_ref_n(v_type_3729_, 2);
v___x_4165_ = l_Lean_mkApp3(v___x_4162_, v___x_4123_, v_type_3729_, v_type_3729_);
lean_inc_ref(v___x_4127_);
v___x_4166_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4165_, v___x_4127_, v___y_4077_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_dec_ref_known(v___x_4166_, 1);
if (lean_obj_tag(v___y_4069_) == 1)
{
lean_object* v_val_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_val_4167_ = lean_ctor_get(v___y_4069_, 0);
lean_inc(v___y_4068_);
v___x_4168_ = l_Lean_mkConst(v___x_4062_, v___y_4068_);
lean_inc_ref(v_type_3729_);
v___x_4169_ = l_Lean_Expr_app___override(v___x_4168_, v_type_3729_);
lean_inc(v_val_4167_);
v___x_4170_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4169_, v_val_4167_, v___y_4077_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_dec_ref_known(v___x_4170_, 1);
v___y_4011_ = v___y_4064_;
v___y_4012_ = v___x_4127_;
v___y_4013_ = v___x_4142_;
v___y_4014_ = v___y_4066_;
v___y_4015_ = v___y_4068_;
v___y_4016_ = v___x_4112_;
v___y_4017_ = v___x_4123_;
v___y_4018_ = v___x_4084_;
v___y_4019_ = v___x_4154_;
v___y_4020_ = v___x_4093_;
v___y_4021_ = v___y_4067_;
v___y_4022_ = v___x_4145_;
v___y_4023_ = v___x_4114_;
v___y_4024_ = v___y_4069_;
v___y_4025_ = v___x_4094_;
v___y_4026_ = v___x_4149_;
v___y_4027_ = v___x_4097_;
v___y_4028_ = v_noNatDivInstQ_x3f_4071_;
v___y_4029_ = v___x_4103_;
v___y_4030_ = v___x_4159_;
v___y_4031_ = v___x_4139_;
v___y_4032_ = v___x_4118_;
v___y_4033_ = v___y_4070_;
v___y_4034_ = v___x_4136_;
v___y_4035_ = v___y_4065_;
v___y_4036_ = v___x_4122_;
v___y_4037_ = v___x_4109_;
v___y_4038_ = v___x_4161_;
v___y_4039_ = v___y_4072_;
v___y_4040_ = v___y_4073_;
v___y_4041_ = v___y_4074_;
v___y_4042_ = v___y_4075_;
v___y_4043_ = v___y_4076_;
v___y_4044_ = v___y_4077_;
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4079_;
v___y_4047_ = v___y_4080_;
v___y_4048_ = v___y_4081_;
goto v___jp_4010_;
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec_ref_known(v___y_4069_, 1);
lean_dec_ref_known(v___x_4161_, 2);
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
v___y_4011_ = v___y_4064_;
v___y_4012_ = v___x_4127_;
v___y_4013_ = v___x_4142_;
v___y_4014_ = v___y_4066_;
v___y_4015_ = v___y_4068_;
v___y_4016_ = v___x_4112_;
v___y_4017_ = v___x_4123_;
v___y_4018_ = v___x_4084_;
v___y_4019_ = v___x_4154_;
v___y_4020_ = v___x_4093_;
v___y_4021_ = v___y_4067_;
v___y_4022_ = v___x_4145_;
v___y_4023_ = v___x_4114_;
v___y_4024_ = v___y_4069_;
v___y_4025_ = v___x_4094_;
v___y_4026_ = v___x_4149_;
v___y_4027_ = v___x_4097_;
v___y_4028_ = v_noNatDivInstQ_x3f_4071_;
v___y_4029_ = v___x_4103_;
v___y_4030_ = v___x_4159_;
v___y_4031_ = v___x_4139_;
v___y_4032_ = v___x_4118_;
v___y_4033_ = v___y_4070_;
v___y_4034_ = v___x_4136_;
v___y_4035_ = v___y_4065_;
v___y_4036_ = v___x_4122_;
v___y_4037_ = v___x_4109_;
v___y_4038_ = v___x_4161_;
v___y_4039_ = v___y_4072_;
v___y_4040_ = v___y_4073_;
v___y_4041_ = v___y_4074_;
v___y_4042_ = v___y_4075_;
v___y_4043_ = v___y_4076_;
v___y_4044_ = v___y_4077_;
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4079_;
v___y_4047_ = v___y_4080_;
v___y_4048_ = v___y_4081_;
goto v___jp_4010_;
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec_ref_known(v___x_4161_, 2);
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4179_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4166_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4166_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v___x_4162_);
lean_dec_ref_known(v___x_4161_, 2);
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4187_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4164_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4164_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref_known(v___x_4144_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4195_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4158_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4158_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref_known(v___x_4144_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4203_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4153_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4153_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec_ref_known(v___x_4145_, 2);
lean_dec_ref_known(v___x_4144_, 2);
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4211_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4148_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4148_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4219_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4141_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4141_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4227_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4135_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4135_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___x_4127_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4112_);
lean_dec_ref(v___x_4109_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4084_);
lean_dec(v_noNatDivInstQ_x3f_4071_);
lean_dec(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec(v___y_4064_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_type_3729_);
v_a_4235_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4131_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4131_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
v___jp_4243_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4261_ = lean_box(0);
lean_inc(v_val_3748_);
v___x_4262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4262_, 0, v_val_3748_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
lean_inc_ref(v___x_4262_);
v___x_4263_ = l_Lean_mkConst(v___x_4260_, v___x_4262_);
lean_inc_ref(v_base_3730_);
v___x_4264_ = l_Lean_Expr_app___override(v___x_4263_, v_base_3730_);
v___x_4265_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4264_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
if (lean_obj_tag(v_a_4266_) == 1)
{
lean_object* v_val_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_val_4267_ = lean_ctor_get(v_a_4266_, 0);
lean_inc(v_val_4267_);
lean_dec_ref_known(v_a_4266_, 1);
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4262_);
v___x_4269_ = l_Lean_mkConst(v___x_4268_, v___x_4262_);
lean_inc_ref(v_base_3730_);
v___x_4270_ = l_Lean_mkAppB(v___x_4269_, v_base_3730_, v_val_4267_);
v___x_4271_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4270_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc(v_a_4272_);
lean_dec_ref_known(v___x_4271_, 1);
if (lean_obj_tag(v_a_4272_) == 1)
{
lean_object* v_val_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_val_4273_ = lean_ctor_get(v_a_4272_, 0);
lean_inc(v_val_4273_);
lean_dec_ref_known(v_a_4272_, 1);
v___x_4274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4262_);
v___x_4275_ = l_Lean_mkConst(v___x_4274_, v___x_4262_);
lean_inc_ref(v_natModuleInst_3731_);
lean_inc_ref(v_base_3730_);
v___x_4276_ = l_Lean_mkAppB(v___x_4275_, v_base_3730_, v_natModuleInst_3731_);
v___x_4277_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4276_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
if (lean_obj_tag(v_a_4278_) == 1)
{
lean_object* v_val_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4289_; 
v_val_4279_ = lean_ctor_get(v_a_4278_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v_a_4278_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4281_ = v_a_4278_;
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_val_4279_);
lean_dec(v_a_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4262_);
v___x_4284_ = l_Lean_mkConst(v___x_4283_, v___x_4262_);
lean_inc_ref(v_natModuleInst_3731_);
lean_inc_ref(v_base_3730_);
v___x_4285_ = l_Lean_mkApp4(v___x_4284_, v_base_3730_, v_natModuleInst_3731_, v_val_4273_, v_val_4279_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4285_);
v___x_4287_ = v___x_4281_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
v___y_4064_ = v_isLinearInstQ_x3f_4249_;
v___y_4065_ = v___y_4245_;
v___y_4066_ = v___y_4244_;
v___y_4067_ = v___y_4246_;
v___y_4068_ = v___x_4262_;
v___y_4069_ = v___y_4247_;
v___y_4070_ = v___y_4248_;
v_noNatDivInstQ_x3f_4071_ = v___x_4287_;
v___y_4072_ = v___y_4250_;
v___y_4073_ = v___y_4251_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4253_;
v___y_4076_ = v___y_4254_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v___y_4079_ = v___y_4257_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
goto v___jp_4063_;
}
}
}
else
{
lean_object* v___x_4290_; 
lean_dec(v_a_4278_);
lean_dec(v_val_4273_);
v___x_4290_ = lean_box(0);
v___y_4064_ = v_isLinearInstQ_x3f_4249_;
v___y_4065_ = v___y_4245_;
v___y_4066_ = v___y_4244_;
v___y_4067_ = v___y_4246_;
v___y_4068_ = v___x_4262_;
v___y_4069_ = v___y_4247_;
v___y_4070_ = v___y_4248_;
v_noNatDivInstQ_x3f_4071_ = v___x_4290_;
v___y_4072_ = v___y_4250_;
v___y_4073_ = v___y_4251_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4253_;
v___y_4076_ = v___y_4254_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v___y_4079_ = v___y_4257_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
goto v___jp_4063_;
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v_val_4273_);
lean_dec_ref_known(v___x_4262_, 2);
lean_dec(v_isLinearInstQ_x3f_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___y_4244_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4291_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4277_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4277_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v___x_4299_; 
lean_dec(v_a_4272_);
v___x_4299_ = lean_box(0);
v___y_4064_ = v_isLinearInstQ_x3f_4249_;
v___y_4065_ = v___y_4245_;
v___y_4066_ = v___y_4244_;
v___y_4067_ = v___y_4246_;
v___y_4068_ = v___x_4262_;
v___y_4069_ = v___y_4247_;
v___y_4070_ = v___y_4248_;
v_noNatDivInstQ_x3f_4071_ = v___x_4299_;
v___y_4072_ = v___y_4250_;
v___y_4073_ = v___y_4251_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4253_;
v___y_4076_ = v___y_4254_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v___y_4079_ = v___y_4257_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
goto v___jp_4063_;
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref_known(v___x_4262_, 2);
lean_dec(v_isLinearInstQ_x3f_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___y_4244_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4300_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4271_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4271_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v___x_4308_; 
lean_dec(v_a_4266_);
v___x_4308_ = lean_box(0);
v___y_4064_ = v_isLinearInstQ_x3f_4249_;
v___y_4065_ = v___y_4245_;
v___y_4066_ = v___y_4244_;
v___y_4067_ = v___y_4246_;
v___y_4068_ = v___x_4262_;
v___y_4069_ = v___y_4247_;
v___y_4070_ = v___y_4248_;
v_noNatDivInstQ_x3f_4071_ = v___x_4308_;
v___y_4072_ = v___y_4250_;
v___y_4073_ = v___y_4251_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4253_;
v___y_4076_ = v___y_4254_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v___y_4079_ = v___y_4257_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
goto v___jp_4063_;
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref_known(v___x_4262_, 2);
lean_dec(v_isLinearInstQ_x3f_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___y_4244_);
lean_del_object(v___x_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4309_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4265_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4265_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
lean_dec(v_a_3744_);
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v___x_4477_ = lean_box(0);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_4477_);
v___x_4479_ = v___x_3746_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec_ref(v_natModuleInst_3731_);
lean_dec_ref(v_base_3730_);
lean_dec_ref(v_type_3729_);
v_a_4482_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_3743_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_3743_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4490_, lean_object* v_base_4491_, lean_object* v_natModuleInst_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4490_, v_base_4491_, v_natModuleInst_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec(v_a_4493_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4525_ = lean_unsigned_to_nat(2u);
v___x_4526_ = l_Lean_Expr_isAppOfArity(v_type_4512_, v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
v___x_4527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4528_ = l_Lean_Expr_appFn_x21(v_type_4512_);
v___x_4529_ = l_Lean_Expr_appArg_x21(v___x_4528_);
lean_dec_ref(v___x_4528_);
v___x_4530_ = l_Lean_Expr_appArg_x21(v_type_4512_);
v___x_4531_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4512_, v___x_4529_, v___x_4530_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec(v_a_4533_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4545_, lean_object* v_a_4546_, lean_object* v_s_4547_){
_start:
{
lean_object* v_structs_4548_; lean_object* v_typeIdOf_4549_; lean_object* v_exprToStructId_4550_; lean_object* v_exprToStructIdEntries_4551_; lean_object* v_forbiddenNatModules_4552_; lean_object* v_natStructs_4553_; lean_object* v_natTypeIdOf_4554_; lean_object* v_exprToNatStructId_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4563_; 
v_structs_4548_ = lean_ctor_get(v_s_4547_, 0);
v_typeIdOf_4549_ = lean_ctor_get(v_s_4547_, 1);
v_exprToStructId_4550_ = lean_ctor_get(v_s_4547_, 2);
v_exprToStructIdEntries_4551_ = lean_ctor_get(v_s_4547_, 3);
v_forbiddenNatModules_4552_ = lean_ctor_get(v_s_4547_, 4);
v_natStructs_4553_ = lean_ctor_get(v_s_4547_, 5);
v_natTypeIdOf_4554_ = lean_ctor_get(v_s_4547_, 6);
v_exprToNatStructId_4555_ = lean_ctor_get(v_s_4547_, 7);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_s_4547_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4557_ = v_s_4547_;
v_isShared_4558_ = v_isSharedCheck_4563_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_exprToNatStructId_4555_);
lean_inc(v_natTypeIdOf_4554_);
lean_inc(v_natStructs_4553_);
lean_inc(v_forbiddenNatModules_4552_);
lean_inc(v_exprToStructIdEntries_4551_);
lean_inc(v_exprToStructId_4550_);
lean_inc(v_typeIdOf_4549_);
lean_inc(v_structs_4548_);
lean_dec(v_s_4547_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4563_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4559_; lean_object* v___x_4561_; 
v___x_4559_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4549_, v_type_4545_, v_a_4546_);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 1, v___x_4559_);
v___x_4561_ = v___x_4557_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_structs_4548_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4562_, 2, v_exprToStructId_4550_);
lean_ctor_set(v_reuseFailAlloc_4562_, 3, v_exprToStructIdEntries_4551_);
lean_ctor_set(v_reuseFailAlloc_4562_, 4, v_forbiddenNatModules_4552_);
lean_ctor_set(v_reuseFailAlloc_4562_, 5, v_natStructs_4553_);
lean_ctor_set(v_reuseFailAlloc_4562_, 6, v_natTypeIdOf_4554_);
lean_ctor_set(v_reuseFailAlloc_4562_, 7, v_exprToNatStructId_4555_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4564_, lean_object* v_vals_4565_, lean_object* v_i_4566_, lean_object* v_k_4567_){
_start:
{
lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4568_ = lean_array_get_size(v_keys_4564_);
v___x_4569_ = lean_nat_dec_lt(v_i_4566_, v___x_4568_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; 
lean_dec(v_i_4566_);
v___x_4570_ = lean_box(0);
return v___x_4570_;
}
else
{
lean_object* v_k_x27_4571_; size_t v___x_4572_; size_t v___x_4573_; uint8_t v___x_4574_; 
v_k_x27_4571_ = lean_array_fget_borrowed(v_keys_4564_, v_i_4566_);
v___x_4572_ = lean_ptr_addr(v_k_4567_);
v___x_4573_ = lean_ptr_addr(v_k_x27_4571_);
v___x_4574_ = lean_usize_dec_eq(v___x_4572_, v___x_4573_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = lean_unsigned_to_nat(1u);
v___x_4576_ = lean_nat_add(v_i_4566_, v___x_4575_);
lean_dec(v_i_4566_);
v_i_4566_ = v___x_4576_;
goto _start;
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4578_ = lean_array_fget_borrowed(v_vals_4565_, v_i_4566_);
lean_dec(v_i_4566_);
lean_inc(v___x_4578_);
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4580_, lean_object* v_vals_4581_, lean_object* v_i_4582_, lean_object* v_k_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4580_, v_vals_4581_, v_i_4582_, v_k_4583_);
lean_dec_ref(v_k_4583_);
lean_dec_ref(v_vals_4581_);
lean_dec_ref(v_keys_4580_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4585_, size_t v_x_4586_, lean_object* v_x_4587_){
_start:
{
if (lean_obj_tag(v_x_4585_) == 0)
{
lean_object* v_es_4588_; lean_object* v___x_4589_; size_t v___x_4590_; size_t v___x_4591_; lean_object* v_j_4592_; lean_object* v___x_4593_; 
v_es_4588_ = lean_ctor_get(v_x_4585_, 0);
v___x_4589_ = lean_box(2);
v___x_4590_ = ((size_t)31ULL);
v___x_4591_ = lean_usize_land(v_x_4586_, v___x_4590_);
v_j_4592_ = lean_usize_to_nat(v___x_4591_);
v___x_4593_ = lean_array_get_borrowed(v___x_4589_, v_es_4588_, v_j_4592_);
lean_dec(v_j_4592_);
switch(lean_obj_tag(v___x_4593_))
{
case 0:
{
lean_object* v_key_4594_; lean_object* v_val_4595_; size_t v___x_4596_; size_t v___x_4597_; uint8_t v___x_4598_; 
v_key_4594_ = lean_ctor_get(v___x_4593_, 0);
v_val_4595_ = lean_ctor_get(v___x_4593_, 1);
v___x_4596_ = lean_ptr_addr(v_x_4587_);
v___x_4597_ = lean_ptr_addr(v_key_4594_);
v___x_4598_ = lean_usize_dec_eq(v___x_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = lean_box(0);
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; 
lean_inc(v_val_4595_);
v___x_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4600_, 0, v_val_4595_);
return v___x_4600_;
}
}
case 1:
{
lean_object* v_node_4601_; size_t v___x_4602_; size_t v___x_4603_; 
v_node_4601_ = lean_ctor_get(v___x_4593_, 0);
v___x_4602_ = ((size_t)5ULL);
v___x_4603_ = lean_usize_shift_right(v_x_4586_, v___x_4602_);
v_x_4585_ = v_node_4601_;
v_x_4586_ = v___x_4603_;
goto _start;
}
default: 
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_box(0);
return v___x_4605_;
}
}
}
else
{
lean_object* v_ks_4606_; lean_object* v_vs_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v_ks_4606_ = lean_ctor_get(v_x_4585_, 0);
v_vs_4607_ = lean_ctor_get(v_x_4585_, 1);
v___x_4608_ = lean_unsigned_to_nat(0u);
v___x_4609_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4606_, v_vs_4607_, v___x_4608_, v_x_4587_);
return v___x_4609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4610_, lean_object* v_x_4611_, lean_object* v_x_4612_){
_start:
{
size_t v_x_6736__boxed_4613_; lean_object* v_res_4614_; 
v_x_6736__boxed_4613_ = lean_unbox_usize(v_x_4611_);
lean_dec(v_x_4611_);
v_res_4614_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4610_, v_x_6736__boxed_4613_, v_x_4612_);
lean_dec_ref(v_x_4612_);
lean_dec_ref(v_x_4610_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4615_, lean_object* v_x_4616_){
_start:
{
size_t v___x_4617_; size_t v___x_4618_; size_t v___x_4619_; uint64_t v___x_4620_; size_t v___x_4621_; lean_object* v___x_4622_; 
v___x_4617_ = lean_ptr_addr(v_x_4616_);
v___x_4618_ = ((size_t)3ULL);
v___x_4619_ = lean_usize_shift_right(v___x_4617_, v___x_4618_);
v___x_4620_ = lean_usize_to_uint64(v___x_4619_);
v___x_4621_ = lean_uint64_to_usize(v___x_4620_);
v___x_4622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4615_, v___x_4621_, v_x_4616_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4623_, lean_object* v_x_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4623_, v_x_4624_);
lean_dec_ref(v_x_4624_);
lean_dec_ref(v_x_4623_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4629_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4708_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4708_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4708_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
uint8_t v_linarith_4643_; 
v_linarith_4643_ = lean_ctor_get_uint8(v_a_4639_, sizeof(void*)*14 + 22);
lean_dec(v_a_4639_);
if (v_linarith_4643_ == 0)
{
lean_object* v___x_4644_; lean_object* v___x_4646_; 
lean_dec_ref(v_type_4626_);
v___x_4644_ = lean_box(0);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4644_);
v___x_4646_ = v___x_4641_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
else
{
lean_object* v___x_4648_; 
lean_del_object(v___x_4641_);
lean_inc_ref(v_type_4626_);
v___x_4648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_4626_, v_a_4629_, v_a_4634_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4699_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4651_ = v___x_4648_;
v_isShared_4652_ = v_isSharedCheck_4699_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4699_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_unbox(v_a_4649_);
lean_dec(v_a_4649_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; 
lean_del_object(v___x_4651_);
v___x_4654_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4627_, v_a_4635_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4686_; 
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4657_ = v___x_4654_;
v_isShared_4658_ = v_isSharedCheck_4686_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4654_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4686_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v_typeIdOf_4659_; lean_object* v___x_4660_; 
v_typeIdOf_4659_ = lean_ctor_get(v_a_4655_, 1);
lean_inc_ref(v_typeIdOf_4659_);
lean_dec(v_a_4655_);
v___x_4660_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4659_, v_type_4626_);
lean_dec_ref(v_typeIdOf_4659_);
if (lean_obj_tag(v___x_4660_) == 1)
{
lean_object* v_val_4661_; lean_object* v___x_4663_; 
lean_dec_ref(v_type_4626_);
v_val_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_val_4661_);
lean_dec_ref_known(v___x_4660_, 1);
if (v_isShared_4658_ == 0)
{
lean_ctor_set(v___x_4657_, 0, v_val_4661_);
v___x_4663_ = v___x_4657_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_val_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
else
{
lean_object* v___x_4665_; 
lean_dec(v___x_4660_);
lean_del_object(v___x_4657_);
lean_inc_ref(v_type_4626_);
v___x_4665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___f_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_n(v_a_4666_, 2);
lean_dec_ref_known(v___x_4665_, 1);
v___f_4667_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4667_, 0, v_type_4626_);
lean_closure_set(v___f_4667_, 1, v_a_4666_);
v___x_4668_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4669_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4668_, v___f_4667_, v_a_4627_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; 
v_unused_4677_ = lean_ctor_get(v___x_4669_, 0);
lean_dec(v_unused_4677_);
v___x_4671_ = v___x_4669_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_dec(v___x_4669_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v_a_4666_);
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4666_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v_a_4666_);
v_a_4678_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4669_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4669_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
else
{
lean_dec_ref(v_type_4626_);
return v___x_4665_;
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v_type_4626_);
v_a_4687_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4654_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4654_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
lean_object* v___x_4695_; lean_object* v___x_4697_; 
lean_dec_ref(v_type_4626_);
v___x_4695_ = lean_box(0);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4695_);
v___x_4697_ = v___x_4651_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec_ref(v_type_4626_);
v_a_4700_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4648_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4648_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec_ref(v_type_4626_);
v_a_4709_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4638_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4638_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
lean_dec(v_a_4719_);
lean_dec(v_a_4718_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4730_, lean_object* v_x_4731_, lean_object* v_x_4732_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4731_, v_x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4734_, lean_object* v_x_4735_, lean_object* v_x_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4734_, v_x_4735_, v_x_4736_);
lean_dec_ref(v_x_4736_);
lean_dec_ref(v_x_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4738_, lean_object* v_x_4739_, size_t v_x_4740_, lean_object* v_x_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4739_, v_x_4740_, v_x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4743_, lean_object* v_x_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_){
_start:
{
size_t v_x_6972__boxed_4747_; lean_object* v_res_4748_; 
v_x_6972__boxed_4747_ = lean_unbox_usize(v_x_4745_);
lean_dec(v_x_4745_);
v_res_4748_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4743_, v_x_4744_, v_x_6972__boxed_4747_, v_x_4746_);
lean_dec_ref(v_x_4746_);
lean_dec_ref(v_x_4744_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4749_, lean_object* v_keys_4750_, lean_object* v_vals_4751_, lean_object* v_heq_4752_, lean_object* v_i_4753_, lean_object* v_k_4754_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4750_, v_vals_4751_, v_i_4753_, v_k_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4756_, lean_object* v_keys_4757_, lean_object* v_vals_4758_, lean_object* v_heq_4759_, lean_object* v_i_4760_, lean_object* v_k_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4756_, v_keys_4757_, v_vals_4758_, v_heq_4759_, v_i_4760_, v_k_4761_);
lean_dec_ref(v_k_4761_);
lean_dec_ref(v_vals_4758_);
lean_dec_ref(v_keys_4757_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4763_, lean_object* v_type_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4772_ = lean_box(0);
v___x_4773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4773_, 0, v_u_4763_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = l_Lean_mkConst(v___x_4771_, v___x_4773_);
v___x_4775_ = l_Lean_Expr_app___override(v___x_4774_, v_type_4764_);
v___x_4776_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4775_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4777_, lean_object* v_type_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4777_, v_type_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
lean_dec(v_a_4783_);
lean_dec_ref(v_a_4782_);
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4786_, lean_object* v_type_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4786_, v_type_4787_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4800_, lean_object* v_type_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4800_, v_type_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec(v_a_4802_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4814_, lean_object* v_s_4815_){
_start:
{
lean_object* v_structs_4816_; lean_object* v_typeIdOf_4817_; lean_object* v_exprToStructId_4818_; lean_object* v_exprToStructIdEntries_4819_; lean_object* v_forbiddenNatModules_4820_; lean_object* v_natStructs_4821_; lean_object* v_natTypeIdOf_4822_; lean_object* v_exprToNatStructId_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4831_; 
v_structs_4816_ = lean_ctor_get(v_s_4815_, 0);
v_typeIdOf_4817_ = lean_ctor_get(v_s_4815_, 1);
v_exprToStructId_4818_ = lean_ctor_get(v_s_4815_, 2);
v_exprToStructIdEntries_4819_ = lean_ctor_get(v_s_4815_, 3);
v_forbiddenNatModules_4820_ = lean_ctor_get(v_s_4815_, 4);
v_natStructs_4821_ = lean_ctor_get(v_s_4815_, 5);
v_natTypeIdOf_4822_ = lean_ctor_get(v_s_4815_, 6);
v_exprToNatStructId_4823_ = lean_ctor_get(v_s_4815_, 7);
v_isSharedCheck_4831_ = !lean_is_exclusive(v_s_4815_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4825_ = v_s_4815_;
v_isShared_4826_ = v_isSharedCheck_4831_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_exprToNatStructId_4823_);
lean_inc(v_natTypeIdOf_4822_);
lean_inc(v_natStructs_4821_);
lean_inc(v_forbiddenNatModules_4820_);
lean_inc(v_exprToStructIdEntries_4819_);
lean_inc(v_exprToStructId_4818_);
lean_inc(v_typeIdOf_4817_);
lean_inc(v_structs_4816_);
lean_dec(v_s_4815_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4831_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_array_push(v_natStructs_4821_, v___x_4814_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 5, v___x_4827_);
v___x_4829_ = v___x_4825_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_structs_4816_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_typeIdOf_4817_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_exprToStructId_4818_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v_exprToStructIdEntries_4819_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_forbiddenNatModules_4820_);
lean_ctor_set(v_reuseFailAlloc_4830_, 5, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4830_, 6, v_natTypeIdOf_4822_);
lean_ctor_set(v_reuseFailAlloc_4830_, 7, v_exprToNatStructId_4823_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_ref_4838_; lean_object* v___x_4839_; lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4848_; 
v_ref_4838_ = lean_ctor_get(v___y_4835_, 2);
v___x_4839_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4842_ = v___x_4839_;
v_isShared_4843_ = v_isSharedCheck_4848_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4848_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4844_; lean_object* v___x_4846_; 
lean_inc(v_ref_4838_);
v___x_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4844_, 0, v_ref_4838_);
lean_ctor_set(v___x_4844_, 1, v_a_4840_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set_tag(v___x_4842_, 1);
lean_ctor_set(v___x_4842_, 0, v___x_4844_);
v___x_4846_ = v___x_4842_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
return v_res_4855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8(void){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7));
v___x_4873_ = l_Lean_stringToMessageData(v___x_4872_);
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v___x_4886_; 
lean_inc_ref(v_type_4874_);
v___x_4886_ = l_Lean_Meta_getDecLevel(v_type_4874_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4888_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_n(v_a_4887_, 2);
lean_dec_ref_known(v___x_4886_, 1);
lean_inc_ref(v_type_4874_);
v___x_4888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4887_, v_type_4874_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_5181_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_5181_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_5181_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
if (lean_obj_tag(v_a_4889_) == 1)
{
lean_object* v_val_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_del_object(v___x_4891_);
v_val_4893_ = lean_ctor_get(v_a_4889_, 0);
lean_inc_n(v_val_4893_, 2);
lean_dec_ref_known(v_a_4889_, 1);
v___x_4894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4895_ = lean_box(0);
lean_inc(v_a_4887_);
v___x_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4896_, 0, v_a_4887_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
lean_inc_ref(v___x_4896_);
v___x_4897_ = l_Lean_mkConst(v___x_4894_, v___x_4896_);
lean_inc_ref(v_type_4874_);
v___x_4898_ = l_Lean_mkAppB(v___x_4897_, v_type_4874_, v_val_4893_);
v___x_4899_ = l_Lean_Meta_Sym_canon(v___x_4898_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4901_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref_known(v___x_4899_, 1);
v___x_4901_ = l_Lean_Meta_Sym_shareCommon(v_a_4900_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4903_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc_n(v_a_4902_, 2);
lean_dec_ref_known(v___x_4901_, 1);
v___x_4903_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4902_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_a_4904_);
lean_dec_ref_known(v___x_4903_, 1);
if (lean_obj_tag(v_a_4904_) == 1)
{
lean_object* v_val_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_5156_; 
v_val_4905_ = lean_ctor_get(v_a_4904_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_a_4904_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_4907_ = v_a_4904_;
v_isShared_4908_ = v_isSharedCheck_5156_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_val_4905_);
lean_dec(v_a_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_5156_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4909_, v_a_4887_, v_type_4874_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4912_, v_a_4887_, v_type_4874_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4915_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc(v_a_4914_);
lean_dec_ref_known(v___x_4913_, 1);
lean_inc(v_a_4911_);
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4915_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_4887_, v_type_4874_, v_a_4911_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
lean_inc(v_a_4911_);
lean_inc(v_a_4914_);
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4917_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_4887_, v_type_4874_, v_a_4914_, v_a_4911_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
lean_inc(v_a_4911_);
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4919_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_4887_, v_type_4874_, v_a_4911_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4921_, v_a_4887_, v_type_4874_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc_n(v_a_4923_, 2);
lean_dec_ref_known(v___x_4922_, 1);
v___x_4924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4896_);
lean_inc_n(v_a_4887_, 2);
v___x_4925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4925_, 0, v_a_4887_);
lean_ctor_set(v___x_4925_, 1, v___x_4896_);
lean_inc_ref(v___x_4925_);
v___x_4926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4926_, 0, v_a_4887_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
v___x_4927_ = l_Lean_mkConst(v___x_4924_, v___x_4926_);
lean_inc_ref_n(v_type_4874_, 3);
v___x_4928_ = l_Lean_mkApp4(v___x_4927_, v_type_4874_, v_type_4874_, v_type_4874_, v_a_4923_);
v___x_4929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4928_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v_orderedAddInst_x3f_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v___y_4940_; lean_object* v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
if (lean_obj_tag(v_a_4911_) == 1)
{
if (lean_obj_tag(v_a_4916_) == 1)
{
lean_object* v_val_5085_; lean_object* v_val_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v_val_5085_ = lean_ctor_get(v_a_4911_, 0);
v_val_5086_ = lean_ctor_get(v_a_4916_, 0);
v___x_5087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4896_);
v___x_5088_ = l_Lean_mkConst(v___x_5087_, v___x_4896_);
lean_inc(v_val_5086_);
lean_inc(v_val_5085_);
lean_inc_ref(v_type_4874_);
v___x_5089_ = l_Lean_mkApp4(v___x_5088_, v_type_4874_, v_a_4923_, v_val_5085_, v_val_5086_);
v___x_5090_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5089_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5090_, 1);
v_orderedAddInst_x3f_4932_ = v_a_5091_;
v___y_4933_ = v_a_4875_;
v___y_4934_ = v_a_4876_;
v___y_4935_ = v_a_4877_;
v___y_4936_ = v_a_4878_;
v___y_4937_ = v_a_4879_;
v___y_4938_ = v_a_4880_;
v___y_4939_ = v_a_4881_;
v___y_4940_ = v_a_4882_;
v___y_4941_ = v_a_4883_;
v___y_4942_ = v_a_4884_;
goto v___jp_4931_;
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec_ref_known(v_a_4916_, 1);
lean_dec_ref_known(v_a_4911_, 1);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4914_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5092_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5090_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5090_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
else
{
lean_dec(v_a_4923_);
v___y_5074_ = v_a_4875_;
v___y_5075_ = v_a_4876_;
v___y_5076_ = v_a_4877_;
v___y_5077_ = v_a_4878_;
v___y_5078_ = v_a_4879_;
v___y_5079_ = v_a_4880_;
v___y_5080_ = v_a_4881_;
v___y_5081_ = v_a_4882_;
v___y_5082_ = v_a_4883_;
v___y_5083_ = v_a_4884_;
goto v___jp_5073_;
}
}
else
{
lean_dec(v_a_4923_);
v___y_5074_ = v_a_4875_;
v___y_5075_ = v_a_4876_;
v___y_5076_ = v_a_4877_;
v___y_5077_ = v_a_4878_;
v___y_5078_ = v_a_4879_;
v___y_5079_ = v_a_4880_;
v___y_5080_ = v_a_4881_;
v___y_5081_ = v_a_4882_;
v___y_5082_ = v_a_4883_;
v___y_5083_ = v_a_4884_;
goto v___jp_5073_;
}
v___jp_4931_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4896_);
v___x_4944_ = l_Lean_mkConst(v___x_4943_, v___x_4896_);
lean_inc_ref(v_type_4874_);
v___x_4945_ = l_Lean_Expr_app___override(v___x_4944_, v_type_4874_);
v___x_4946_ = l_Lean_Meta_Sym_synthInstance(v___x_4945_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4896_);
v___x_4949_ = l_Lean_mkConst(v___x_4948_, v___x_4896_);
lean_inc_ref(v_type_4874_);
v___x_4950_ = l_Lean_mkAppB(v___x_4949_, v_type_4874_, v_a_4947_);
v___x_4951_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4950_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_a_4952_);
lean_dec_ref_known(v___x_4951_, 1);
v___x_4953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4896_);
v___x_4954_ = l_Lean_mkConst(v___x_4953_, v___x_4896_);
lean_inc(v_val_4893_);
lean_inc_ref(v_type_4874_);
v___x_4955_ = l_Lean_mkAppB(v___x_4954_, v_type_4874_, v_val_4893_);
v___x_4956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4955_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v___x_4958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4958_, v_a_4887_, v_type_4874_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4960_);
lean_dec_ref_known(v___x_4959_, 1);
v___x_4961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_4962_ = l_Lean_mkConst(v___x_4961_, v___x_4896_);
lean_inc_ref(v_type_4874_);
v___x_4963_ = l_Lean_mkAppB(v___x_4962_, v_type_4874_, v_a_4960_);
v___x_4964_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4963_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4966_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
lean_inc_ref(v_type_4874_);
lean_inc(v_a_4887_);
v___x_4966_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4887_, v_type_4874_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4966_, 1);
v___x_4968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
lean_ctor_set(v___x_4970_, 1, v___x_4925_);
v___x_4971_ = l_Lean_mkConst(v___x_4968_, v___x_4970_);
v___x_4972_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4874_, 2);
v___x_4973_ = l_Lean_mkApp4(v___x_4971_, v___x_4972_, v_type_4874_, v_type_4874_, v_a_4967_);
v___x_4974_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4973_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4933_, v___y_4941_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v_natStructs_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___f_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
v_natStructs_4978_ = lean_ctor_get(v_a_4977_, 5);
lean_inc_ref(v_natStructs_4978_);
lean_dec(v_a_4977_);
v___x_4979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4887_);
v___x_4980_ = l_Lean_Level_succ___override(v_a_4887_);
v___x_4981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
lean_ctor_set(v___x_4981_, 1, v___x_4895_);
v___x_4982_ = l_Lean_mkConst(v___x_4979_, v___x_4981_);
v___x_4983_ = l_Lean_Expr_app___override(v___x_4982_, v_a_4902_);
v___x_4984_ = lean_array_get_size(v_natStructs_4978_);
lean_dec_ref(v_natStructs_4978_);
v___x_4985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6);
v___x_4986_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set(v___x_4986_, 1, v_val_4905_);
lean_ctor_set(v___x_4986_, 2, v_type_4874_);
lean_ctor_set(v___x_4986_, 3, v_a_4887_);
lean_ctor_set(v___x_4986_, 4, v_val_4893_);
lean_ctor_set(v___x_4986_, 5, v_a_4911_);
lean_ctor_set(v___x_4986_, 6, v_a_4914_);
lean_ctor_set(v___x_4986_, 7, v_a_4918_);
lean_ctor_set(v___x_4986_, 8, v_a_4916_);
lean_ctor_set(v___x_4986_, 9, v_orderedAddInst_x3f_4932_);
lean_ctor_set(v___x_4986_, 10, v_a_4920_);
lean_ctor_set(v___x_4986_, 11, v_a_4952_);
lean_ctor_set(v___x_4986_, 12, v___x_4983_);
lean_ctor_set(v___x_4986_, 13, v_a_4965_);
lean_ctor_set(v___x_4986_, 14, v_a_4957_);
lean_ctor_set(v___x_4986_, 15, v_a_4930_);
lean_ctor_set(v___x_4986_, 16, v_a_4975_);
lean_ctor_set(v___x_4986_, 17, v___x_4985_);
v___f_4987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4987_, 0, v___x_4986_);
v___x_4988_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4989_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4988_, v___f_4987_, v___y_4933_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4999_; 
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; 
v_unused_5000_ = lean_ctor_get(v___x_4989_, 0);
lean_dec(v_unused_5000_);
v___x_4991_ = v___x_4989_;
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
else
{
lean_dec(v___x_4989_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4984_);
v___x_4994_ = v___x_4907_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4984_);
v___x_4994_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4996_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 0, v___x_4994_);
v___x_4996_ = v___x_4991_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_del_object(v___x_4907_);
v_a_5001_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_4989_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4989_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
lean_dec(v_a_4975_);
lean_dec(v_a_4965_);
lean_dec(v_a_4957_);
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5009_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_4976_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_4976_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
lean_dec(v_a_4965_);
lean_dec(v_a_4957_);
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5017_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_4974_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_4974_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_dec(v_a_4965_);
lean_dec(v_a_4957_);
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5025_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_4966_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_4966_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
lean_dec(v_a_4957_);
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5033_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_4964_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_4964_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec(v_a_4957_);
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5041_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_4959_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_4959_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec(v_a_4952_);
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5049_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_4956_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_4956_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5057_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___x_4951_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_4951_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_dec(v_orderedAddInst_x3f_4932_);
lean_dec(v_a_4930_);
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5065_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_4946_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_4946_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
v___jp_5073_:
{
lean_object* v___x_5084_; 
v___x_5084_ = lean_box(0);
v_orderedAddInst_x3f_4932_ = v___x_5084_;
v___y_4933_ = v___y_5074_;
v___y_4934_ = v___y_5075_;
v___y_4935_ = v___y_5076_;
v___y_4936_ = v___y_5077_;
v___y_4937_ = v___y_5078_;
v___y_4938_ = v___y_5079_;
v___y_4939_ = v___y_5080_;
v___y_4940_ = v___y_5081_;
v___y_4941_ = v___y_5082_;
v___y_4942_ = v___y_5083_;
goto v___jp_4931_;
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_dec_ref_known(v___x_4925_, 2);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5100_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_4929_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_4929_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_dec(v_a_4920_);
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5108_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_4922_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_4922_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec(v_a_4918_);
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5116_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_4919_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_4919_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
lean_dec(v_a_4916_);
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5124_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_4917_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_4917_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec(v_a_4914_);
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5132_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_4915_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_4915_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_dec(v_a_4911_);
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5140_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_4913_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_4913_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_del_object(v___x_4907_);
lean_dec(v_val_4905_);
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5148_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_4910_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_4910_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_dec(v_a_4904_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v___x_5157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8);
v___x_5158_ = l_Lean_indentExpr(v_a_4902_);
v___x_5159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5157_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5159_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
return v___x_5160_;
}
}
else
{
lean_dec(v_a_4902_);
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
return v___x_4903_;
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5161_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_4901_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_4901_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec_ref_known(v___x_4896_, 2);
lean_dec(v_val_4893_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5169_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_4899_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_4899_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
else
{
lean_object* v___x_5177_; lean_object* v___x_5179_; 
lean_dec(v_a_4889_);
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v___x_5177_ = lean_box(0);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_5177_);
v___x_5179_ = v___x_4891_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5177_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v_a_4887_);
lean_dec_ref(v_type_4874_);
v_a_5182_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_4888_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_4888_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec_ref(v_type_4874_);
v_a_5190_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_4886_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_4886_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec_ref(v_a_5205_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec(v_a_5200_);
lean_dec(v_a_5199_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5211_, lean_object* v_msg_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5212_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5225_, lean_object* v_msg_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5225_, v_msg_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v___y_5228_);
lean_dec(v___y_5227_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5239_, lean_object* v_a_5240_, lean_object* v_s_5241_){
_start:
{
lean_object* v_structs_5242_; lean_object* v_typeIdOf_5243_; lean_object* v_exprToStructId_5244_; lean_object* v_exprToStructIdEntries_5245_; lean_object* v_forbiddenNatModules_5246_; lean_object* v_natStructs_5247_; lean_object* v_natTypeIdOf_5248_; lean_object* v_exprToNatStructId_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5257_; 
v_structs_5242_ = lean_ctor_get(v_s_5241_, 0);
v_typeIdOf_5243_ = lean_ctor_get(v_s_5241_, 1);
v_exprToStructId_5244_ = lean_ctor_get(v_s_5241_, 2);
v_exprToStructIdEntries_5245_ = lean_ctor_get(v_s_5241_, 3);
v_forbiddenNatModules_5246_ = lean_ctor_get(v_s_5241_, 4);
v_natStructs_5247_ = lean_ctor_get(v_s_5241_, 5);
v_natTypeIdOf_5248_ = lean_ctor_get(v_s_5241_, 6);
v_exprToNatStructId_5249_ = lean_ctor_get(v_s_5241_, 7);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_s_5241_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5251_ = v_s_5241_;
v_isShared_5252_ = v_isSharedCheck_5257_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_exprToNatStructId_5249_);
lean_inc(v_natTypeIdOf_5248_);
lean_inc(v_natStructs_5247_);
lean_inc(v_forbiddenNatModules_5246_);
lean_inc(v_exprToStructIdEntries_5245_);
lean_inc(v_exprToStructId_5244_);
lean_inc(v_typeIdOf_5243_);
lean_inc(v_structs_5242_);
lean_dec(v_s_5241_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5257_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5253_; lean_object* v___x_5255_; 
v___x_5253_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5248_, v_type_5239_, v_a_5240_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 6, v___x_5253_);
v___x_5255_ = v___x_5251_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_structs_5242_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v_typeIdOf_5243_);
lean_ctor_set(v_reuseFailAlloc_5256_, 2, v_exprToStructId_5244_);
lean_ctor_set(v_reuseFailAlloc_5256_, 3, v_exprToStructIdEntries_5245_);
lean_ctor_set(v_reuseFailAlloc_5256_, 4, v_forbiddenNatModules_5246_);
lean_ctor_set(v_reuseFailAlloc_5256_, 5, v_natStructs_5247_);
lean_ctor_set(v_reuseFailAlloc_5256_, 6, v___x_5253_);
lean_ctor_set(v_reuseFailAlloc_5256_, 7, v_exprToNatStructId_5249_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5258_, lean_object* v_i_5259_, lean_object* v_k_5260_){
_start:
{
lean_object* v___x_5261_; uint8_t v___x_5262_; 
v___x_5261_ = lean_array_get_size(v_keys_5258_);
v___x_5262_ = lean_nat_dec_lt(v_i_5259_, v___x_5261_);
if (v___x_5262_ == 0)
{
lean_dec(v_i_5259_);
return v___x_5262_;
}
else
{
lean_object* v_k_x27_5263_; size_t v___x_5264_; size_t v___x_5265_; uint8_t v___x_5266_; 
v_k_x27_5263_ = lean_array_fget_borrowed(v_keys_5258_, v_i_5259_);
v___x_5264_ = lean_ptr_addr(v_k_5260_);
v___x_5265_ = lean_ptr_addr(v_k_x27_5263_);
v___x_5266_ = lean_usize_dec_eq(v___x_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = lean_unsigned_to_nat(1u);
v___x_5268_ = lean_nat_add(v_i_5259_, v___x_5267_);
lean_dec(v_i_5259_);
v_i_5259_ = v___x_5268_;
goto _start;
}
else
{
lean_dec(v_i_5259_);
return v___x_5262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5270_, lean_object* v_i_5271_, lean_object* v_k_5272_){
_start:
{
uint8_t v_res_5273_; lean_object* v_r_5274_; 
v_res_5273_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5270_, v_i_5271_, v_k_5272_);
lean_dec_ref(v_k_5272_);
lean_dec_ref(v_keys_5270_);
v_r_5274_ = lean_box(v_res_5273_);
return v_r_5274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5275_, size_t v_x_5276_, lean_object* v_x_5277_){
_start:
{
if (lean_obj_tag(v_x_5275_) == 0)
{
lean_object* v_es_5278_; lean_object* v___x_5279_; size_t v___x_5280_; size_t v___x_5281_; lean_object* v_j_5282_; lean_object* v___x_5283_; 
v_es_5278_ = lean_ctor_get(v_x_5275_, 0);
v___x_5279_ = lean_box(2);
v___x_5280_ = ((size_t)31ULL);
v___x_5281_ = lean_usize_land(v_x_5276_, v___x_5280_);
v_j_5282_ = lean_usize_to_nat(v___x_5281_);
v___x_5283_ = lean_array_get_borrowed(v___x_5279_, v_es_5278_, v_j_5282_);
lean_dec(v_j_5282_);
switch(lean_obj_tag(v___x_5283_))
{
case 0:
{
lean_object* v_key_5284_; size_t v___x_5285_; size_t v___x_5286_; uint8_t v___x_5287_; 
v_key_5284_ = lean_ctor_get(v___x_5283_, 0);
v___x_5285_ = lean_ptr_addr(v_x_5277_);
v___x_5286_ = lean_ptr_addr(v_key_5284_);
v___x_5287_ = lean_usize_dec_eq(v___x_5285_, v___x_5286_);
return v___x_5287_;
}
case 1:
{
lean_object* v_node_5288_; size_t v___x_5289_; size_t v___x_5290_; 
v_node_5288_ = lean_ctor_get(v___x_5283_, 0);
v___x_5289_ = ((size_t)5ULL);
v___x_5290_ = lean_usize_shift_right(v_x_5276_, v___x_5289_);
v_x_5275_ = v_node_5288_;
v_x_5276_ = v___x_5290_;
goto _start;
}
default: 
{
uint8_t v___x_5292_; 
v___x_5292_ = 0;
return v___x_5292_;
}
}
}
else
{
lean_object* v_ks_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v_ks_5293_ = lean_ctor_get(v_x_5275_, 0);
v___x_5294_ = lean_unsigned_to_nat(0u);
v___x_5295_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5293_, v___x_5294_, v_x_5277_);
return v___x_5295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5296_, lean_object* v_x_5297_, lean_object* v_x_5298_){
_start:
{
size_t v_x_8671__boxed_5299_; uint8_t v_res_5300_; lean_object* v_r_5301_; 
v_x_8671__boxed_5299_ = lean_unbox_usize(v_x_5297_);
lean_dec(v_x_5297_);
v_res_5300_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5296_, v_x_8671__boxed_5299_, v_x_5298_);
lean_dec_ref(v_x_5298_);
lean_dec_ref(v_x_5296_);
v_r_5301_ = lean_box(v_res_5300_);
return v_r_5301_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5302_, lean_object* v_x_5303_){
_start:
{
size_t v___x_5304_; size_t v___x_5305_; size_t v___x_5306_; uint64_t v___x_5307_; size_t v___x_5308_; uint8_t v___x_5309_; 
v___x_5304_ = lean_ptr_addr(v_x_5303_);
v___x_5305_ = ((size_t)3ULL);
v___x_5306_ = lean_usize_shift_right(v___x_5304_, v___x_5305_);
v___x_5307_ = lean_usize_to_uint64(v___x_5306_);
v___x_5308_ = lean_uint64_to_usize(v___x_5307_);
v___x_5309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5302_, v___x_5308_, v_x_5303_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5310_, lean_object* v_x_5311_){
_start:
{
uint8_t v_res_5312_; lean_object* v_r_5313_; 
v_res_5312_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5310_, v_x_5311_);
lean_dec_ref(v_x_5311_);
lean_dec_ref(v_x_5310_);
v_r_5313_ = lean_box(v_res_5312_);
return v_r_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5317_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5416_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5416_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5416_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
uint8_t v_linarith_5331_; 
v_linarith_5331_ = lean_ctor_get_uint8(v_a_5327_, sizeof(void*)*14 + 22);
lean_dec(v_a_5327_);
if (v_linarith_5331_ == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5334_; 
lean_dec_ref(v_type_5314_);
v___x_5332_ = lean_box(0);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5332_);
v___x_5334_ = v___x_5329_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5332_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
else
{
lean_object* v___x_5336_; 
lean_del_object(v___x_5329_);
v___x_5336_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5315_, v_a_5323_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5407_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5339_ = v___x_5336_;
v_isShared_5340_ = v_isSharedCheck_5407_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5336_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5407_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v_forbiddenNatModules_5341_; uint8_t v___x_5342_; 
v_forbiddenNatModules_5341_ = lean_ctor_get(v_a_5337_, 4);
lean_inc_ref(v_forbiddenNatModules_5341_);
lean_dec(v_a_5337_);
v___x_5342_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5341_, v_type_5314_);
lean_dec_ref(v_forbiddenNatModules_5341_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5343_; 
lean_del_object(v___x_5339_);
lean_inc_ref(v_type_5314_);
v___x_5343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_5314_, v_a_5317_, v_a_5322_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5394_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5346_ = v___x_5343_;
v_isShared_5347_ = v_isSharedCheck_5394_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5343_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5394_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
uint8_t v___x_5348_; 
v___x_5348_ = lean_unbox(v_a_5344_);
lean_dec(v_a_5344_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; 
lean_del_object(v___x_5346_);
v___x_5349_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5315_, v_a_5323_);
if (lean_obj_tag(v___x_5349_) == 0)
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5381_; 
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5352_ = v___x_5349_;
v_isShared_5353_ = v_isSharedCheck_5381_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5349_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5381_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v_natTypeIdOf_5354_; lean_object* v___x_5355_; 
v_natTypeIdOf_5354_ = lean_ctor_get(v_a_5350_, 6);
lean_inc_ref(v_natTypeIdOf_5354_);
lean_dec(v_a_5350_);
v___x_5355_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5354_, v_type_5314_);
lean_dec_ref(v_natTypeIdOf_5354_);
if (lean_obj_tag(v___x_5355_) == 1)
{
lean_object* v_val_5356_; lean_object* v___x_5358_; 
lean_dec_ref(v_type_5314_);
v_val_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_val_5356_);
lean_dec_ref_known(v___x_5355_, 1);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 0, v_val_5356_);
v___x_5358_ = v___x_5352_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_val_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
else
{
lean_object* v___x_5360_; 
lean_dec(v___x_5355_);
lean_del_object(v___x_5352_);
lean_inc_ref(v_type_5314_);
v___x_5360_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v___f_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc_n(v_a_5361_, 2);
lean_dec_ref_known(v___x_5360_, 1);
v___f_5362_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5362_, 0, v_type_5314_);
lean_closure_set(v___f_5362_, 1, v_a_5361_);
v___x_5363_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5363_, v___f_5362_, v_a_5315_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v___x_5364_, 0);
lean_dec(v_unused_5372_);
v___x_5366_ = v___x_5364_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_dec(v___x_5364_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
lean_ctor_set(v___x_5366_, 0, v_a_5361_);
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5361_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec(v_a_5361_);
v_a_5373_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5364_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5364_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
else
{
lean_dec_ref(v_type_5314_);
return v___x_5360_;
}
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec_ref(v_type_5314_);
v_a_5382_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5349_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5349_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
else
{
lean_object* v___x_5390_; lean_object* v___x_5392_; 
lean_dec_ref(v_type_5314_);
v___x_5390_ = lean_box(0);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 0, v___x_5390_);
v___x_5392_ = v___x_5346_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
lean_dec_ref(v_type_5314_);
v_a_5395_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5397_ = v___x_5343_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5343_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
lean_object* v___x_5403_; lean_object* v___x_5405_; 
lean_dec_ref(v_type_5314_);
v___x_5403_ = lean_box(0);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v___x_5403_);
v___x_5405_ = v___x_5339_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec_ref(v_type_5314_);
v_a_5408_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5336_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5336_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
lean_dec_ref(v_type_5314_);
v_a_5417_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5326_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5326_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
lean_dec(v_a_5431_);
lean_dec_ref(v_a_5430_);
lean_dec(v_a_5429_);
lean_dec_ref(v_a_5428_);
lean_dec(v_a_5427_);
lean_dec(v_a_5426_);
return v_res_5437_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5438_, lean_object* v_x_5439_, lean_object* v_x_5440_){
_start:
{
uint8_t v___x_5441_; 
v___x_5441_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5439_, v_x_5440_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5442_, lean_object* v_x_5443_, lean_object* v_x_5444_){
_start:
{
uint8_t v_res_5445_; lean_object* v_r_5446_; 
v_res_5445_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5442_, v_x_5443_, v_x_5444_);
lean_dec_ref(v_x_5444_);
lean_dec_ref(v_x_5443_);
v_r_5446_ = lean_box(v_res_5445_);
return v_r_5446_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5447_, lean_object* v_x_5448_, size_t v_x_5449_, lean_object* v_x_5450_){
_start:
{
uint8_t v___x_5451_; 
v___x_5451_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5448_, v_x_5449_, v_x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5452_, lean_object* v_x_5453_, lean_object* v_x_5454_, lean_object* v_x_5455_){
_start:
{
size_t v_x_8939__boxed_5456_; uint8_t v_res_5457_; lean_object* v_r_5458_; 
v_x_8939__boxed_5456_ = lean_unbox_usize(v_x_5454_);
lean_dec(v_x_5454_);
v_res_5457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5452_, v_x_5453_, v_x_8939__boxed_5456_, v_x_5455_);
lean_dec_ref(v_x_5455_);
lean_dec_ref(v_x_5453_);
v_r_5458_ = lean_box(v_res_5457_);
return v_r_5458_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5459_, lean_object* v_keys_5460_, lean_object* v_vals_5461_, lean_object* v_heq_5462_, lean_object* v_i_5463_, lean_object* v_k_5464_){
_start:
{
uint8_t v___x_5465_; 
v___x_5465_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5460_, v_i_5463_, v_k_5464_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5466_, lean_object* v_keys_5467_, lean_object* v_vals_5468_, lean_object* v_heq_5469_, lean_object* v_i_5470_, lean_object* v_k_5471_){
_start:
{
uint8_t v_res_5472_; lean_object* v_r_5473_; 
v_res_5472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5466_, v_keys_5467_, v_vals_5468_, v_heq_5469_, v_i_5470_, v_k_5471_);
lean_dec_ref(v_k_5471_);
lean_dec_ref(v_vals_5468_);
lean_dec_ref(v_keys_5467_);
v_r_5473_ = lean_box(v_res_5472_);
return v_r_5473_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
}
#ifdef __cplusplus
}
#endif
