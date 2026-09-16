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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7;
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
size_t v_x_283__boxed_378_; size_t v_x_284__boxed_379_; lean_object* v_res_380_; 
v_x_283__boxed_378_ = lean_unbox_usize(v_x_376_);
lean_dec(v_x_376_);
v_x_284__boxed_379_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_res_380_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_372_, v___x_373_, v___x_374_, v_x_375_, v_x_283__boxed_378_, v_x_284__boxed_379_);
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
size_t v_x_266__boxed_611_; size_t v_x_267__boxed_612_; lean_object* v_res_613_; 
v_x_266__boxed_611_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_x_267__boxed_612_ = lean_unbox_usize(v_x_610_);
lean_dec(v_x_610_);
v_res_613_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_607_, v_x_608_, v_x_266__boxed_611_, v_x_267__boxed_612_);
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
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_816_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_816_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; 
v___x_811_ = lean_unbox(v_a_807_);
lean_dec(v_a_807_);
if (v___x_811_ == 0)
{
lean_del_object(v___x_809_);
goto v___jp_799_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_box(v_lia_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
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
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_type_795_);
v_a_817_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_803_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_803_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg___boxed(lean_object* v_type_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_830_, v_a_833_, v_a_838_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_856_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_895_; 
v_val_868_ = lean_ctor_get(v_ringId_x3f_856_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_ringId_x3f_856_);
if (v_isSharedCheck_895_ == 0)
{
v___x_870_ = v_ringId_x3f_856_;
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_val_868_);
lean_dec(v_ringId_x3f_856_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = 0;
v___x_873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_873_, 0, v_val_868_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*1, v___x_872_);
v___x_874_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_873_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec_ref_known(v___x_873_, 1);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_886_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_commRingInst_879_; lean_object* v___x_881_; 
v_commRingInst_879_ = lean_ctor_get(v_a_875_, 4);
lean_inc_ref(v_commRingInst_879_);
lean_dec(v_a_875_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v_commRingInst_879_);
v___x_881_ = v___x_870_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_commRingInst_879_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_870_);
v_a_887_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_874_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_874_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_ringId_x3f_856_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_925_, lean_object* v_type_926_, lean_object* v_commRingInst_x3f_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_927_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_947_; 
v_val_934_ = lean_ctor_get(v_commRingInst_x3f_927_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_commRingInst_x3f_927_);
if (v_isSharedCheck_947_ == 0)
{
v___x_936_ = v_commRingInst_x3f_927_;
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v_commRingInst_x3f_927_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_947_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v_u_925_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_mkConst(v___x_938_, v___x_940_);
v___x_942_ = l_Lean_mkAppB(v___x_941_, v_type_926_, v_val_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_942_);
v___x_944_ = v___x_936_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_commRingInst_x3f_927_);
v___x_948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v_u_925_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_mkConst(v___x_948_, v___x_950_);
v___x_952_ = l_Lean_Expr_app___override(v___x_951_, v_type_926_);
v___x_953_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_952_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_954_, lean_object* v_type_955_, lean_object* v_commRingInst_x3f_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_954_, v_type_955_, v_commRingInst_x3f_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_964_, lean_object* v_type_965_, lean_object* v_commRingInst_x3f_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_964_, v_type_965_, v_commRingInst_x3f_966_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_979_, lean_object* v_type_980_, lean_object* v_commRingInst_x3f_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_979_, v_type_980_, v_commRingInst_x3f_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec(v_a_982_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_1005_, lean_object* v_type_1006_, lean_object* v_ringInst_x3f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1007_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1027_; 
v_val_1014_ = lean_ctor_get(v_ringInst_x3f_1007_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_ringInst_x3f_1007_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1016_ = v_ringInst_x3f_1007_;
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_val_1014_);
lean_dec(v_ringInst_x3f_1007_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_u_1005_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_mkConst(v___x_1018_, v___x_1020_);
v___x_1022_ = l_Lean_mkAppB(v___x_1021_, v_type_1006_, v_val_1014_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1022_);
v___x_1024_ = v___x_1016_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec(v_ringInst_x3f_1007_);
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_u_1005_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_mkConst(v___x_1028_, v___x_1030_);
v___x_1032_ = l_Lean_Expr_app___override(v___x_1031_, v_type_1006_);
v___x_1033_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1032_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1034_, lean_object* v_type_1035_, lean_object* v_ringInst_x3f_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1034_, v_type_1035_, v_ringInst_x3f_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1044_, lean_object* v_type_1045_, lean_object* v_ringInst_x3f_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1044_, v_type_1045_, v_ringInst_x3f_1046_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1059_, lean_object* v_type_1060_, lean_object* v_ringInst_x3f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1059_, v_type_1060_, v_ringInst_x3f_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec(v_a_1062_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1085_, lean_object* v_type_1086_, lean_object* v_ringInst_x3f_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1087_) == 1)
{
lean_object* v_val_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1107_; 
v_val_1094_ = lean_ctor_get(v_ringInst_x3f_1087_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_ringInst_x3f_1087_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1096_ = v_ringInst_x3f_1087_;
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_val_1094_);
lean_dec(v_ringInst_x3f_1087_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1107_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_u_1085_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_mkConst(v___x_1098_, v___x_1100_);
v___x_1102_ = l_Lean_mkAppB(v___x_1101_, v_type_1086_, v_val_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1102_);
v___x_1104_ = v___x_1096_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v_ringInst_x3f_1087_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_u_1085_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_mkConst(v___x_1108_, v___x_1110_);
v___x_1112_ = l_Lean_Expr_app___override(v___x_1111_, v_type_1086_);
v___x_1113_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1112_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1114_, lean_object* v_type_1115_, lean_object* v_ringInst_x3f_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1114_, v_type_1115_, v_ringInst_x3f_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1124_, lean_object* v_type_1125_, lean_object* v_ringInst_x3f_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1124_, v_type_1125_, v_ringInst_x3f_1126_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1139_, lean_object* v_type_1140_, lean_object* v_ringInst_x3f_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1139_, v_type_1140_, v_ringInst_x3f_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1161_, lean_object* v_type_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_u_1161_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_inc_ref(v___x_1176_);
v___x_1177_ = l_Lean_mkConst(v___x_1174_, v___x_1176_);
lean_inc_ref(v_type_1162_);
v___x_1178_ = l_Lean_Expr_app___override(v___x_1177_, v_type_1162_);
v___x_1179_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1178_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1261_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1261_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1261_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_val_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1256_; 
lean_del_object(v___x_1182_);
v_val_1184_ = lean_ctor_get(v_a_1180_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1186_ = v_a_1180_;
v_isShared_1187_ = v_isSharedCheck_1256_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_val_1184_);
lean_dec(v_a_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1256_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1189_ = l_Lean_mkConst(v___x_1188_, v___x_1176_);
lean_inc_ref(v_type_1162_);
v___x_1190_ = l_Lean_mkAppB(v___x_1189_, v_type_1162_, v_val_1184_);
v___x_1191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1190_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1247_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1247_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1247_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = l_Lean_Meta_mkNumeral(v_type_1162_, v___x_1203_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_n(v_a_1205_, 2);
lean_dec_ref_known(v___x_1204_, 1);
lean_inc(v_a_1192_);
v___x_1206_ = l_Lean_Meta_isDefEqD(v_a_1192_, v_a_1205_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; uint8_t v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = lean_unbox(v_a_1207_);
lean_dec(v_a_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1211_; 
lean_inc(v_a_1192_);
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1192_, v_a_1205_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1167_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; uint8_t v_verbose_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v_verbose_1213_ = lean_ctor_get_uint8(v_a_1212_, 0);
lean_dec(v_a_1212_);
if (v_verbose_1213_ == 0)
{
lean_dec(v_a_1210_);
goto v___jp_1196_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_Meta_Sym_reportIssue(v_a_1210_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec_ref_known(v___x_1214_, 1);
goto v___jp_1196_;
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
lean_del_object(v___x_1186_);
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
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
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1210_);
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
lean_del_object(v___x_1186_);
v_a_1223_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1211_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1211_);
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
lean_dec(v_a_1205_);
goto v___jp_1196_;
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1205_);
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
lean_del_object(v___x_1186_);
v_a_1231_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1206_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1206_);
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
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_del_object(v___x_1194_);
lean_dec(v_a_1192_);
lean_del_object(v___x_1186_);
v_a_1239_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1204_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1204_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
v___jp_1196_:
{
lean_object* v___x_1198_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v_a_1192_);
v___x_1198_ = v___x_1186_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1192_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_del_object(v___x_1186_);
lean_dec_ref(v_type_1162_);
v_a_1248_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1191_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1191_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_dec(v_a_1180_);
lean_dec_ref_known(v___x_1176_, 2);
lean_dec_ref(v_type_1162_);
v___x_1257_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1257_);
v___x_1259_ = v___x_1182_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1176_, 2);
lean_dec_ref(v_type_1162_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1262_, lean_object* v_type_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1262_, v_type_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec(v_a_1264_);
return v_res_1275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1284_, lean_object* v_type_1285_, lean_object* v_semiringInst_x3f_1286_, lean_object* v_leInst_x3f_1287_, lean_object* v_ltInst_x3f_1288_, lean_object* v_preorderInst_x3f_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1286_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1287_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1288_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1289_) == 1)
{
lean_object* v_val_1300_; lean_object* v_val_1301_; lean_object* v_val_1302_; lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_isOrdType_1308_; lean_object* v___x_1309_; 
v_val_1300_ = lean_ctor_get(v_semiringInst_x3f_1286_, 0);
lean_inc(v_val_1300_);
lean_dec_ref_known(v_semiringInst_x3f_1286_, 1);
v_val_1301_ = lean_ctor_get(v_leInst_x3f_1287_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v_leInst_x3f_1287_, 1);
v_val_1302_ = lean_ctor_get(v_ltInst_x3f_1288_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_ltInst_x3f_1288_, 1);
v_val_1303_ = lean_ctor_get(v_preorderInst_x3f_1289_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_preorderInst_x3f_1289_, 1);
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_u_1284_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_mkConst(v___x_1304_, v___x_1306_);
v_isOrdType_1308_ = l_Lean_mkApp5(v___x_1307_, v_type_1285_, v_val_1300_, v_val_1301_, v_val_1302_, v_val_1303_);
lean_inc_ref(v_isOrdType_1308_);
v___x_1309_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1308_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
if (lean_obj_tag(v_a_1310_) == 1)
{
lean_dec_ref_known(v_a_1310_, 1);
lean_dec_ref(v_isOrdType_1308_);
return v___x_1309_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref_known(v___x_1309_, 1);
lean_dec(v_a_1310_);
v___x_1311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1312_ = l_Lean_indentExpr(v_isOrdType_1308_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1290_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v_verbose_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v_verbose_1316_ = lean_ctor_get_uint8(v_a_1315_, 0);
lean_dec(v_a_1315_);
if (v_verbose_1316_ == 0)
{
lean_dec_ref_known(v___x_1313_, 2);
goto v___jp_1297_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_Sym_reportIssue(v___x_1313_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_dec_ref_known(v___x_1317_, 1);
goto v___jp_1297_;
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
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
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref_known(v___x_1313_, 2);
v_a_1326_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1314_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1314_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
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
}
else
{
lean_dec_ref(v_isOrdType_1308_);
return v___x_1309_;
}
}
else
{
lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref_known(v_leInst_x3f_1287_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1286_, 1);
lean_dec(v_preorderInst_x3f_1289_);
lean_dec_ref(v_type_1285_);
lean_dec(v_u_1284_);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_ltInst_x3f_1288_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_ltInst_x3f_1288_, 0);
lean_dec(v_unused_1342_);
v___x_1335_ = v_ltInst_x3f_1288_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v_ltInst_x3f_1288_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref_known(v_semiringInst_x3f_1286_, 1);
lean_dec(v_preorderInst_x3f_1289_);
lean_dec(v_ltInst_x3f_1288_);
lean_dec_ref(v_type_1285_);
lean_dec(v_u_1284_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_leInst_x3f_1287_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_leInst_x3f_1287_, 0);
lean_dec(v_unused_1351_);
v___x_1344_ = v_leInst_x3f_1287_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v_leInst_x3f_1287_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_box(0);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_preorderInst_x3f_1289_);
lean_dec(v_ltInst_x3f_1288_);
lean_dec(v_leInst_x3f_1287_);
lean_dec_ref(v_type_1285_);
lean_dec(v_u_1284_);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_semiringInst_x3f_1286_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v_semiringInst_x3f_1286_, 0);
lean_dec(v_unused_1360_);
v___x_1353_ = v_semiringInst_x3f_1286_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v_semiringInst_x3f_1286_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_box(0);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_preorderInst_x3f_1289_);
lean_dec(v_ltInst_x3f_1288_);
lean_dec(v_leInst_x3f_1287_);
lean_dec(v_semiringInst_x3f_1286_);
lean_dec_ref(v_type_1285_);
lean_dec(v_u_1284_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
v___jp_1297_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1363_, lean_object* v_type_1364_, lean_object* v_semiringInst_x3f_1365_, lean_object* v_leInst_x3f_1366_, lean_object* v_ltInst_x3f_1367_, lean_object* v_preorderInst_x3f_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1363_, v_type_1364_, v_semiringInst_x3f_1365_, v_leInst_x3f_1366_, v_ltInst_x3f_1367_, v_preorderInst_x3f_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1377_, lean_object* v_type_1378_, lean_object* v_semiringInst_x3f_1379_, lean_object* v_leInst_x3f_1380_, lean_object* v_ltInst_x3f_1381_, lean_object* v_preorderInst_x3f_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1377_, v_type_1378_, v_semiringInst_x3f_1379_, v_leInst_x3f_1380_, v_ltInst_x3f_1381_, v_preorderInst_x3f_1382_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1395_ = _args[0];
lean_object* v_type_1396_ = _args[1];
lean_object* v_semiringInst_x3f_1397_ = _args[2];
lean_object* v_leInst_x3f_1398_ = _args[3];
lean_object* v_ltInst_x3f_1399_ = _args[4];
lean_object* v_preorderInst_x3f_1400_ = _args[5];
lean_object* v_a_1401_ = _args[6];
lean_object* v_a_1402_ = _args[7];
lean_object* v_a_1403_ = _args[8];
lean_object* v_a_1404_ = _args[9];
lean_object* v_a_1405_ = _args[10];
lean_object* v_a_1406_ = _args[11];
lean_object* v_a_1407_ = _args[12];
lean_object* v_a_1408_ = _args[13];
lean_object* v_a_1409_ = _args[14];
lean_object* v_a_1410_ = _args[15];
lean_object* v_a_1411_ = _args[16];
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1395_, v_type_1396_, v_semiringInst_x3f_1397_, v_leInst_x3f_1398_, v_ltInst_x3f_1399_, v_preorderInst_x3f_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec(v_a_1401_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1423_, lean_object* v_type_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_natModuleType_1435_; lean_object* v___x_1436_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_u_1423_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_inc_ref(v___x_1433_);
v___x_1434_ = l_Lean_mkConst(v___x_1431_, v___x_1433_);
lean_inc_ref(v_type_1424_);
v_natModuleType_1435_ = l_Lean_Expr_app___override(v___x_1434_, v_type_1424_);
v___x_1436_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1435_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1450_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1450_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1450_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
if (lean_obj_tag(v_a_1437_) == 1)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_del_object(v___x_1439_);
v_val_1441_ = lean_ctor_get(v_a_1437_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v_a_1437_, 1);
v___x_1442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1443_ = l_Lean_mkConst(v___x_1442_, v___x_1433_);
v___x_1444_ = l_Lean_mkAppB(v___x_1443_, v_type_1424_, v_val_1441_);
v___x_1445_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1444_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_dec(v_a_1437_);
lean_dec_ref_known(v___x_1433_, 2);
lean_dec_ref(v_type_1424_);
v___x_1446_ = lean_box(0);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1446_);
v___x_1448_ = v___x_1439_;
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
}
else
{
lean_dec_ref_known(v___x_1433_, 2);
lean_dec_ref(v_type_1424_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1451_, lean_object* v_type_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1451_, v_type_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1460_, lean_object* v_type_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1460_, v_type_1461_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1474_, lean_object* v_type_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1474_, v_type_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec(v_a_1476_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1488_, lean_object* v_u_1489_, lean_object* v_type_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_u_1489_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Lean_mkConst(v_declName_1488_, v___x_1498_);
v___x_1500_ = l_Lean_Expr_app___override(v___x_1499_, v_type_1490_);
v___x_1501_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1500_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1502_, lean_object* v_u_1503_, lean_object* v_type_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1502_, v_u_1503_, v_type_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1512_, lean_object* v_u_1513_, lean_object* v_type_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1512_, v_u_1513_, v_type_1514_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1527_, lean_object* v_u_1528_, lean_object* v_type_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1527_, v_u_1528_, v_type_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec(v_a_1530_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1542_, lean_object* v_u_1543_, lean_object* v_type_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_u_1543_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_mkConst(v_declName_1542_, v___x_1553_);
v___x_1555_ = l_Lean_Expr_app___override(v___x_1554_, v_type_1544_);
v___x_1556_ = l_Lean_Meta_Sym_synthInstance(v___x_1555_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1557_, lean_object* v_u_1558_, lean_object* v_type_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1557_, v_u_1558_, v_type_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1568_, lean_object* v_u_1569_, lean_object* v_type_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1568_, v_u_1569_, v_type_1570_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1583_, lean_object* v_u_1584_, lean_object* v_type_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1583_, v_u_1584_, v_type_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec(v_a_1586_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1598_, lean_object* v_u_1599_, lean_object* v_type_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1608_ = lean_box(0);
lean_inc_n(v_u_1599_, 2);
v___x_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_u_1599_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_u_1599_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_u_1599_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_mkConst(v_declName_1598_, v___x_1611_);
lean_inc_ref_n(v_type_1600_, 2);
v___x_1613_ = l_Lean_mkApp3(v___x_1612_, v_type_1600_, v_type_1600_, v_type_1600_);
v___x_1614_ = l_Lean_Meta_Sym_synthInstance(v___x_1613_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1615_, lean_object* v_u_1616_, lean_object* v_type_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1615_, v_u_1616_, v_type_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1626_, lean_object* v_u_1627_, lean_object* v_type_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1626_, v_u_1627_, v_type_1628_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1641_, lean_object* v_u_1642_, lean_object* v_type_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1641_, v_u_1642_, v_type_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
return v_res_1655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = l_Lean_Level_ofNat(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1661_, lean_object* v_type_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1672_ = lean_box(0);
lean_inc(v_u_1661_);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_u_1661_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_u_1661_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1671_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_mkConst(v___x_1670_, v___x_1675_);
v___x_1677_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1662_);
v___x_1678_ = l_Lean_mkApp3(v___x_1676_, v___x_1677_, v_type_1662_, v_type_1662_);
v___x_1679_ = l_Lean_Meta_Sym_synthInstance(v___x_1678_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1680_, lean_object* v_type_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1680_, v_type_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1690_, lean_object* v_type_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1690_, v_type_1691_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1704_, lean_object* v_type_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1704_, v_type_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_a_1706_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1718_, lean_object* v_type_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1729_ = lean_box(0);
lean_inc(v_u_1718_);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_u_1718_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_u_1718_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1728_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_mkConst(v___x_1727_, v___x_1732_);
v___x_1734_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1719_);
v___x_1735_ = l_Lean_mkApp3(v___x_1733_, v___x_1734_, v_type_1719_, v_type_1719_);
v___x_1736_ = l_Lean_Meta_Sym_synthInstance(v___x_1735_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1737_, lean_object* v_type_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1737_, v_type_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1747_, lean_object* v_type_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1747_, v_type_1748_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1761_, lean_object* v_type_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1761_, v_type_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec(v_a_1763_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1775_, lean_object* v_parentInst_x3f_1776_, lean_object* v_childInst_x3f_1777_, lean_object* v_toFieldName_1778_, lean_object* v_u_1779_, lean_object* v_type_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1775_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1776_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1777_) == 1)
{
lean_object* v_val_1791_; lean_object* v_val_1792_; lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_toField_1797_; lean_object* v___x_1798_; 
v_val_1791_ = lean_ctor_get(v_leInst_x3f_1775_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v_leInst_x3f_1775_, 1);
v_val_1792_ = lean_ctor_get(v_parentInst_x3f_1776_, 0);
lean_inc_n(v_val_1792_, 2);
lean_dec_ref_known(v_parentInst_x3f_1776_, 1);
v_val_1793_ = lean_ctor_get(v_childInst_x3f_1777_, 0);
v___x_1794_ = lean_box(0);
v___x_1795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_u_1779_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_mkConst(v_toFieldName_1778_, v___x_1795_);
lean_inc(v_val_1793_);
v_toField_1797_ = l_Lean_mkApp3(v___x_1796_, v_type_1780_, v_val_1791_, v_val_1793_);
lean_inc_ref(v_toField_1797_);
v___x_1798_ = l_Lean_Meta_isDefEqD(v_val_1792_, v_toField_1797_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1829_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1829_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1829_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v_a_1805_; lean_object* v___x_1806_; 
lean_del_object(v___x_1801_);
lean_dec_ref_known(v_childInst_x3f_1777_, 1);
v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1792_, v_toField_1797_);
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1781_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; uint8_t v_verbose_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v_verbose_1808_ = lean_ctor_get_uint8(v_a_1807_, 0);
lean_dec(v_a_1807_);
if (v_verbose_1808_ == 0)
{
lean_dec(v_a_1805_);
goto v___jp_1788_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Meta_Sym_reportIssue(v_a_1805_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_dec_ref_known(v___x_1809_, 1);
goto v___jp_1788_;
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
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
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1805_);
v_a_1818_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1806_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
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
lean_object* v___x_1827_; 
lean_dec_ref(v_toField_1797_);
lean_dec(v_val_1792_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v_childInst_x3f_1777_);
v___x_1827_ = v___x_1801_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_childInst_x3f_1777_);
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
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_toField_1797_);
lean_dec(v_val_1792_);
lean_dec_ref_known(v_childInst_x3f_1777_, 1);
v_a_1830_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1798_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1798_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
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
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref_known(v_leInst_x3f_1775_, 1);
lean_dec_ref(v_type_1780_);
lean_dec(v_u_1779_);
lean_dec(v_toFieldName_1778_);
lean_dec(v_childInst_x3f_1777_);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_parentInst_x3f_1776_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v_parentInst_x3f_1776_, 0);
lean_dec(v_unused_1846_);
v___x_1839_ = v_parentInst_x3f_1776_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v_parentInst_x3f_1776_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_box(0);
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_type_1780_);
lean_dec(v_u_1779_);
lean_dec(v_toFieldName_1778_);
lean_dec(v_childInst_x3f_1777_);
lean_dec(v_parentInst_x3f_1776_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_leInst_x3f_1775_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_leInst_x3f_1775_, 0);
lean_dec(v_unused_1855_);
v___x_1848_ = v_leInst_x3f_1775_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v_leInst_x3f_1775_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
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
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec_ref(v_type_1780_);
lean_dec(v_u_1779_);
lean_dec(v_toFieldName_1778_);
lean_dec(v_childInst_x3f_1777_);
lean_dec(v_parentInst_x3f_1776_);
lean_dec(v_leInst_x3f_1775_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
v___jp_1788_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1858_, lean_object* v_parentInst_x3f_1859_, lean_object* v_childInst_x3f_1860_, lean_object* v_toFieldName_1861_, lean_object* v_u_1862_, lean_object* v_type_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1858_, v_parentInst_x3f_1859_, v_childInst_x3f_1860_, v_toFieldName_1861_, v_u_1862_, v_type_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1872_, lean_object* v_parentInst_x3f_1873_, lean_object* v_childInst_x3f_1874_, lean_object* v_toFieldName_1875_, lean_object* v_u_1876_, lean_object* v_type_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1872_, v_parentInst_x3f_1873_, v_childInst_x3f_1874_, v_toFieldName_1875_, v_u_1876_, v_type_1877_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1890_ = _args[0];
lean_object* v_parentInst_x3f_1891_ = _args[1];
lean_object* v_childInst_x3f_1892_ = _args[2];
lean_object* v_toFieldName_1893_ = _args[3];
lean_object* v_u_1894_ = _args[4];
lean_object* v_type_1895_ = _args[5];
lean_object* v_a_1896_ = _args[6];
lean_object* v_a_1897_ = _args[7];
lean_object* v_a_1898_ = _args[8];
lean_object* v_a_1899_ = _args[9];
lean_object* v_a_1900_ = _args[10];
lean_object* v_a_1901_ = _args[11];
lean_object* v_a_1902_ = _args[12];
lean_object* v_a_1903_ = _args[13];
lean_object* v_a_1904_ = _args[14];
lean_object* v_a_1905_ = _args[15];
lean_object* v_a_1906_ = _args[16];
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1890_, v_parentInst_x3f_1891_, v_childInst_x3f_1892_, v_toFieldName_1893_, v_u_1894_, v_type_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1908_, lean_object* v_inst_1909_, lean_object* v_toFieldName_1910_, lean_object* v_u_1911_, lean_object* v_type_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_toField_1921_; lean_object* v___x_1922_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_u_1911_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_mkConst(v_toFieldName_1910_, v___x_1919_);
v_toField_1921_ = l_Lean_mkAppB(v___x_1920_, v_type_1912_, v_inst_1909_);
v___x_1922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1908_, v_toField_1921_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1923_, lean_object* v_inst_1924_, lean_object* v_toFieldName_1925_, lean_object* v_u_1926_, lean_object* v_type_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1923_, v_inst_1924_, v_toFieldName_1925_, v_u_1926_, v_type_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1934_, lean_object* v_inst_1935_, lean_object* v_toFieldName_1936_, lean_object* v_u_1937_, lean_object* v_type_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1934_, v_inst_1935_, v_toFieldName_1936_, v_u_1937_, v_type_1938_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1951_, lean_object* v_inst_1952_, lean_object* v_toFieldName_1953_, lean_object* v_u_1954_, lean_object* v_type_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1951_, v_inst_1952_, v_toFieldName_1953_, v_u_1954_, v_type_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
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
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1968_, lean_object* v_inst_1969_, lean_object* v_toFieldName_1970_, lean_object* v_toHeteroName_1971_, lean_object* v_u_1972_, lean_object* v_type_1973_, lean_object* v_extraType_x3f_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_toField_1983_; 
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_u_1972_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
lean_inc_ref(v___x_1981_);
v___x_1982_ = l_Lean_mkConst(v_toFieldName_1970_, v___x_1981_);
lean_inc_ref(v_type_1973_);
v_toField_1983_ = l_Lean_mkAppB(v___x_1982_, v_type_1973_, v_inst_1969_);
if (lean_obj_tag(v_extraType_x3f_1974_) == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = l_Lean_mkConst(v_toHeteroName_1971_, v___x_1981_);
v___x_1985_ = l_Lean_mkAppB(v___x_1984_, v_type_1973_, v_toField_1983_);
v___x_1986_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1968_, v___x_1985_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1986_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_val_1987_ = lean_ctor_get(v_extraType_x3f_1974_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v_extraType_x3f_1974_, 1);
v___x_1988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1981_);
v___x_1990_ = l_Lean_mkConst(v_toHeteroName_1971_, v___x_1989_);
v___x_1991_ = l_Lean_mkApp3(v___x_1990_, v_val_1987_, v_type_1973_, v_toField_1983_);
v___x_1992_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1968_, v___x_1991_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1993_, lean_object* v_inst_1994_, lean_object* v_toFieldName_1995_, lean_object* v_toHeteroName_1996_, lean_object* v_u_1997_, lean_object* v_type_1998_, lean_object* v_extraType_x3f_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1993_, v_inst_1994_, v_toFieldName_1995_, v_toHeteroName_1996_, v_u_1997_, v_type_1998_, v_extraType_x3f_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_2006_, lean_object* v_inst_2007_, lean_object* v_toFieldName_2008_, lean_object* v_toHeteroName_2009_, lean_object* v_u_2010_, lean_object* v_type_2011_, lean_object* v_extraType_x3f_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_2006_, v_inst_2007_, v_toFieldName_2008_, v_toHeteroName_2009_, v_u_2010_, v_type_2011_, v_extraType_x3f_2012_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_2025_ = _args[0];
lean_object* v_inst_2026_ = _args[1];
lean_object* v_toFieldName_2027_ = _args[2];
lean_object* v_toHeteroName_2028_ = _args[3];
lean_object* v_u_2029_ = _args[4];
lean_object* v_type_2030_ = _args[5];
lean_object* v_extraType_x3f_2031_ = _args[6];
lean_object* v_a_2032_ = _args[7];
lean_object* v_a_2033_ = _args[8];
lean_object* v_a_2034_ = _args[9];
lean_object* v_a_2035_ = _args[10];
lean_object* v_a_2036_ = _args[11];
lean_object* v_a_2037_ = _args[12];
lean_object* v_a_2038_ = _args[13];
lean_object* v_a_2039_ = _args[14];
lean_object* v_a_2040_ = _args[15];
lean_object* v_a_2041_ = _args[16];
lean_object* v_a_2042_ = _args[17];
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2025_, v_inst_2026_, v_toFieldName_2027_, v_toHeteroName_2028_, v_u_2029_, v_type_2030_, v_extraType_x3f_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec(v_a_2032_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2048_, lean_object* v_type_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_smulType_2065_; lean_object* v___x_2066_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2059_ = lean_box(0);
lean_inc(v_u_2048_);
v___x_2060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_u_2048_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_u_2048_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2058_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_inc_ref(v___x_2062_);
v___x_2063_ = l_Lean_mkConst(v___x_2057_, v___x_2062_);
v___x_2064_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2049_, 2);
v_smulType_2065_ = l_Lean_mkApp3(v___x_2063_, v___x_2064_, v_type_2049_, v_type_2049_);
v___x_2066_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2065_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2103_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2103_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2103_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2098_; 
lean_del_object(v___x_2069_);
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2073_ = v_a_2067_;
v_isShared_2074_ = v_isSharedCheck_2098_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v_a_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2098_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2076_ = l_Lean_mkConst(v___x_2075_, v___x_2062_);
lean_inc_ref(v_type_2049_);
v___x_2077_ = l_Lean_mkApp4(v___x_2076_, v___x_2064_, v_type_2049_, v_type_2049_, v_val_2071_);
v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2077_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v_a_2079_);
v___x_2084_ = v___x_2073_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2084_);
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_del_object(v___x_2073_);
v_a_2090_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2078_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2078_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
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
else
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec(v_a_2067_);
lean_dec_ref_known(v___x_2062_, 2);
lean_dec_ref(v_type_2049_);
v___x_2099_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2099_);
v___x_2101_ = v___x_2069_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2062_, 2);
lean_dec_ref(v_type_2049_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2104_, lean_object* v_type_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2104_, v_type_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2114_, lean_object* v_type_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2114_, v_type_2115_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2128_, lean_object* v_type_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2128_, v_type_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec(v_a_2130_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2142_, lean_object* v_type_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_smulType_2159_; lean_object* v___x_2160_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2153_ = lean_box(0);
lean_inc(v_u_2142_);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_u_2142_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_u_2142_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2152_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
lean_inc_ref(v___x_2156_);
v___x_2157_ = l_Lean_mkConst(v___x_2151_, v___x_2156_);
v___x_2158_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2143_, 2);
v_smulType_2159_ = l_Lean_mkApp3(v___x_2157_, v___x_2158_, v_type_2143_, v_type_2143_);
v___x_2160_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2159_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2197_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2197_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2197_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
if (lean_obj_tag(v_a_2161_) == 1)
{
lean_object* v_val_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2163_);
v_val_2165_ = lean_ctor_get(v_a_2161_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2167_ = v_a_2161_;
v_isShared_2168_ = v_isSharedCheck_2192_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_val_2165_);
lean_dec(v_a_2161_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2192_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2170_ = l_Lean_mkConst(v___x_2169_, v___x_2156_);
lean_inc_ref(v_type_2143_);
v___x_2171_ = l_Lean_mkApp4(v___x_2170_, v___x_2158_, v_type_2143_, v_type_2143_, v_val_2165_);
v___x_2172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2171_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2183_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_a_2173_);
v___x_2178_ = v___x_2167_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_del_object(v___x_2167_);
v_a_2184_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2172_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2172_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_a_2161_);
lean_dec_ref_known(v___x_2156_, 2);
lean_dec_ref(v_type_2143_);
v___x_2193_ = lean_box(0);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2193_);
v___x_2195_ = v___x_2163_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2156_, 2);
lean_dec_ref(v_type_2143_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2198_, lean_object* v_type_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2198_, v_type_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2208_, lean_object* v_type_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2208_, v_type_2209_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2222_, lean_object* v_type_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2222_, v_type_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec(v_a_2224_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v_ks_2240_; lean_object* v_vs_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2267_; 
v_ks_2240_ = lean_ctor_get(v_x_2236_, 0);
v_vs_2241_ = lean_ctor_get(v_x_2236_, 1);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_x_2236_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2243_ = v_x_2236_;
v_isShared_2244_ = v_isSharedCheck_2267_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_vs_2241_);
lean_inc(v_ks_2240_);
lean_dec(v_x_2236_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2267_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_array_get_size(v_ks_2240_);
v___x_2246_ = lean_nat_dec_lt(v_x_2237_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec(v_x_2237_);
v___x_2247_ = lean_array_push(v_ks_2240_, v_x_2238_);
v___x_2248_ = lean_array_push(v_vs_2241_, v_x_2239_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2248_);
lean_ctor_set(v___x_2243_, 0, v___x_2247_);
v___x_2250_ = v___x_2243_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v_k_x27_2252_; size_t v___x_2253_; size_t v___x_2254_; uint8_t v___x_2255_; 
v_k_x27_2252_ = lean_array_fget_borrowed(v_ks_2240_, v_x_2237_);
v___x_2253_ = lean_ptr_addr(v_x_2238_);
v___x_2254_ = lean_ptr_addr(v_k_x27_2252_);
v___x_2255_ = lean_usize_dec_eq(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2257_; 
if (v_isShared_2244_ == 0)
{
v___x_2257_ = v___x_2243_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_ks_2240_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_vs_2241_);
v___x_2257_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_add(v_x_2237_, v___x_2258_);
lean_dec(v_x_2237_);
v_x_2236_ = v___x_2257_;
v_x_2237_ = v___x_2259_;
goto _start;
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = lean_array_fset(v_ks_2240_, v_x_2237_, v_x_2238_);
v___x_2263_ = lean_array_fset(v_vs_2241_, v_x_2237_, v_x_2239_);
lean_dec(v_x_2237_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2263_);
lean_ctor_set(v___x_2243_, 0, v___x_2262_);
v___x_2265_ = v___x_2243_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2268_, lean_object* v_k_2269_, lean_object* v_v_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2268_, v___x_2271_, v_k_2269_, v_v_2270_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2274_, size_t v_x_2275_, size_t v_x_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
if (lean_obj_tag(v_x_2274_) == 0)
{
lean_object* v_es_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v_j_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_es_2279_ = lean_ctor_get(v_x_2274_, 0);
v___x_2280_ = ((size_t)31ULL);
v___x_2281_ = lean_usize_land(v_x_2275_, v___x_2280_);
v_j_2282_ = lean_usize_to_nat(v___x_2281_);
v___x_2283_ = lean_array_get_size(v_es_2279_);
v___x_2284_ = lean_nat_dec_lt(v_j_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec(v_j_2282_);
lean_dec(v_x_2278_);
lean_dec_ref(v_x_2277_);
return v_x_2274_;
}
else
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2325_; 
lean_inc_ref(v_es_2279_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2274_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_x_2274_, 0);
lean_dec(v_unused_2326_);
v___x_2286_ = v_x_2274_;
v_isShared_2287_ = v_isSharedCheck_2325_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_x_2274_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2325_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_v_2288_; lean_object* v___x_2289_; lean_object* v_xs_x27_2290_; lean_object* v___y_2292_; 
v_v_2288_ = lean_array_fget(v_es_2279_, v_j_2282_);
v___x_2289_ = lean_box(0);
v_xs_x27_2290_ = lean_array_fset(v_es_2279_, v_j_2282_, v___x_2289_);
switch(lean_obj_tag(v_v_2288_))
{
case 0:
{
lean_object* v_key_2297_; lean_object* v_val_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2310_; 
v_key_2297_ = lean_ctor_get(v_v_2288_, 0);
v_val_2298_ = lean_ctor_get(v_v_2288_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_v_2288_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2300_ = v_v_2288_;
v_isShared_2301_ = v_isSharedCheck_2310_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_val_2298_);
lean_inc(v_key_2297_);
lean_dec(v_v_2288_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2310_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
size_t v___x_2302_; size_t v___x_2303_; uint8_t v___x_2304_; 
v___x_2302_ = lean_ptr_addr(v_x_2277_);
v___x_2303_ = lean_ptr_addr(v_key_2297_);
v___x_2304_ = lean_usize_dec_eq(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_del_object(v___x_2300_);
v___x_2305_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2297_, v_val_2298_, v_x_2277_, v_x_2278_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
v___y_2292_ = v___x_2306_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2308_; 
lean_dec(v_val_2298_);
lean_dec(v_key_2297_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v_x_2278_);
lean_ctor_set(v___x_2300_, 0, v_x_2277_);
v___x_2308_ = v___x_2300_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_x_2277_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_x_2278_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
v___y_2292_ = v___x_2308_;
goto v___jp_2291_;
}
}
}
}
case 1:
{
lean_object* v_node_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2323_; 
v_node_2311_ = lean_ctor_get(v_v_2288_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_v_2288_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2313_ = v_v_2288_;
v_isShared_2314_ = v_isSharedCheck_2323_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_node_2311_);
lean_dec(v_v_2288_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2323_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2315_ = ((size_t)5ULL);
v___x_2316_ = lean_usize_shift_right(v_x_2275_, v___x_2315_);
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_add(v_x_2276_, v___x_2317_);
v___x_2319_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2311_, v___x_2316_, v___x_2318_, v_x_2277_, v_x_2278_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2319_);
v___x_2321_ = v___x_2313_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
v___y_2292_ = v___x_2321_;
goto v___jp_2291_;
}
}
}
default: 
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_x_2277_);
lean_ctor_set(v___x_2324_, 1, v_x_2278_);
v___y_2292_ = v___x_2324_;
goto v___jp_2291_;
}
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = lean_array_fset(v_xs_x27_2290_, v_j_2282_, v___y_2292_);
lean_dec(v_j_2282_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2293_);
v___x_2295_ = v___x_2286_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
else
{
lean_object* v_ks_2327_; lean_object* v_vs_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2346_; 
v_ks_2327_ = lean_ctor_get(v_x_2274_, 0);
v_vs_2328_ = lean_ctor_get(v_x_2274_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_x_2274_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2330_ = v_x_2274_;
v_isShared_2331_ = v_isSharedCheck_2346_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_vs_2328_);
lean_inc(v_ks_2327_);
lean_dec(v_x_2274_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2346_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_ks_2327_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_vs_2328_);
v___x_2333_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v_newNode_2334_; size_t v___x_2335_; uint8_t v___x_2336_; 
v_newNode_2334_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2333_, v_x_2277_, v_x_2278_);
v___x_2335_ = ((size_t)7ULL);
v___x_2336_ = lean_usize_dec_le(v___x_2335_, v_x_2276_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2334_);
v___x_2338_ = lean_unsigned_to_nat(4u);
v___x_2339_ = lean_nat_dec_lt(v___x_2337_, v___x_2338_);
lean_dec(v___x_2337_);
if (v___x_2339_ == 0)
{
lean_object* v_ks_2340_; lean_object* v_vs_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_ks_2340_ = lean_ctor_get(v_newNode_2334_, 0);
lean_inc_ref(v_ks_2340_);
v_vs_2341_ = lean_ctor_get(v_newNode_2334_, 1);
lean_inc_ref(v_vs_2341_);
lean_dec_ref(v_newNode_2334_);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2276_, v_ks_2340_, v_vs_2341_, v___x_2342_, v___x_2343_);
lean_dec_ref(v_vs_2341_);
lean_dec_ref(v_ks_2340_);
return v___x_2344_;
}
else
{
return v_newNode_2334_;
}
}
else
{
return v_newNode_2334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2347_, lean_object* v_keys_2348_, lean_object* v_vals_2349_, lean_object* v_i_2350_, lean_object* v_entries_2351_){
_start:
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = lean_array_get_size(v_keys_2348_);
v___x_2353_ = lean_nat_dec_lt(v_i_2350_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec(v_i_2350_);
return v_entries_2351_;
}
else
{
lean_object* v_k_2354_; lean_object* v_v_2355_; size_t v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; uint64_t v___x_2359_; size_t v_h_2360_; size_t v___x_2361_; lean_object* v___x_2362_; size_t v___x_2363_; size_t v___x_2364_; size_t v___x_2365_; size_t v_h_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_k_2354_ = lean_array_fget_borrowed(v_keys_2348_, v_i_2350_);
v_v_2355_ = lean_array_fget_borrowed(v_vals_2349_, v_i_2350_);
v___x_2356_ = lean_ptr_addr(v_k_2354_);
v___x_2357_ = ((size_t)3ULL);
v___x_2358_ = lean_usize_shift_right(v___x_2356_, v___x_2357_);
v___x_2359_ = lean_usize_to_uint64(v___x_2358_);
v_h_2360_ = lean_uint64_to_usize(v___x_2359_);
v___x_2361_ = ((size_t)5ULL);
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_sub(v_depth_2347_, v___x_2363_);
v___x_2365_ = lean_usize_mul(v___x_2361_, v___x_2364_);
v_h_2366_ = lean_usize_shift_right(v_h_2360_, v___x_2365_);
v___x_2367_ = lean_nat_add(v_i_2350_, v___x_2362_);
lean_dec(v_i_2350_);
lean_inc(v_v_2355_);
lean_inc(v_k_2354_);
v___x_2368_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2351_, v_h_2366_, v_depth_2347_, v_k_2354_, v_v_2355_);
v_i_2350_ = v___x_2367_;
v_entries_2351_ = v___x_2368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2370_, lean_object* v_keys_2371_, lean_object* v_vals_2372_, lean_object* v_i_2373_, lean_object* v_entries_2374_){
_start:
{
size_t v_depth_boxed_2375_; lean_object* v_res_2376_; 
v_depth_boxed_2375_ = lean_unbox_usize(v_depth_2370_);
lean_dec(v_depth_2370_);
v_res_2376_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2375_, v_keys_2371_, v_vals_2372_, v_i_2373_, v_entries_2374_);
lean_dec_ref(v_vals_2372_);
lean_dec_ref(v_keys_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
size_t v_x_526710__boxed_2382_; size_t v_x_526711__boxed_2383_; lean_object* v_res_2384_; 
v_x_526710__boxed_2382_ = lean_unbox_usize(v_x_2378_);
lean_dec(v_x_2378_);
v_x_526711__boxed_2383_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_res_2384_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2377_, v_x_526710__boxed_2382_, v_x_526711__boxed_2383_, v_x_2380_, v_x_2381_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
size_t v___x_2388_; size_t v___x_2389_; size_t v___x_2390_; uint64_t v___x_2391_; size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2388_ = lean_ptr_addr(v_x_2386_);
v___x_2389_ = ((size_t)3ULL);
v___x_2390_ = lean_usize_shift_right(v___x_2388_, v___x_2389_);
v___x_2391_ = lean_usize_to_uint64(v___x_2390_);
v___x_2392_ = lean_uint64_to_usize(v___x_2391_);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2385_, v___x_2392_, v___x_2393_, v_x_2386_, v_x_2387_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2395_, lean_object* v_s_2396_){
_start:
{
lean_object* v_structs_2397_; lean_object* v_typeIdOf_2398_; lean_object* v_exprToStructId_2399_; lean_object* v_exprToStructIdEntries_2400_; lean_object* v_forbiddenNatModules_2401_; lean_object* v_natStructs_2402_; lean_object* v_natTypeIdOf_2403_; lean_object* v_exprToNatStructId_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2413_; 
v_structs_2397_ = lean_ctor_get(v_s_2396_, 0);
v_typeIdOf_2398_ = lean_ctor_get(v_s_2396_, 1);
v_exprToStructId_2399_ = lean_ctor_get(v_s_2396_, 2);
v_exprToStructIdEntries_2400_ = lean_ctor_get(v_s_2396_, 3);
v_forbiddenNatModules_2401_ = lean_ctor_get(v_s_2396_, 4);
v_natStructs_2402_ = lean_ctor_get(v_s_2396_, 5);
v_natTypeIdOf_2403_ = lean_ctor_get(v_s_2396_, 6);
v_exprToNatStructId_2404_ = lean_ctor_get(v_s_2396_, 7);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_s_2396_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2406_ = v_s_2396_;
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_exprToNatStructId_2404_);
lean_inc(v_natTypeIdOf_2403_);
lean_inc(v_natStructs_2402_);
lean_inc(v_forbiddenNatModules_2401_);
lean_inc(v_exprToStructIdEntries_2400_);
lean_inc(v_exprToStructId_2399_);
lean_inc(v_typeIdOf_2398_);
lean_inc(v_structs_2397_);
lean_dec(v_s_2396_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2401_, v_type_2395_, v___x_2408_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2409_);
v___x_2411_ = v___x_2406_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_structs_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_typeIdOf_2398_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_exprToStructId_2399_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_exprToStructIdEntries_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2412_, 5, v_natStructs_2402_);
lean_ctor_set(v_reuseFailAlloc_2412_, 6, v_natTypeIdOf_2403_);
lean_ctor_set(v_reuseFailAlloc_2412_, 7, v_exprToNatStructId_2404_);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v_a_2414_, lean_object* v_00___2415_){
_start:
{
if (lean_obj_tag(v_a_2414_) == 0)
{
uint8_t v___x_2416_; 
v___x_2416_ = 0;
return v___x_2416_;
}
else
{
uint8_t v___x_2417_; 
v___x_2417_ = 1;
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2___boxed(lean_object* v_a_2418_, lean_object* v_00___2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2418_, v_00___2419_);
lean_dec(v_a_2418_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v___x_2422_, lean_object* v_s_2423_){
_start:
{
lean_object* v_structs_2424_; lean_object* v_typeIdOf_2425_; lean_object* v_exprToStructId_2426_; lean_object* v_exprToStructIdEntries_2427_; lean_object* v_forbiddenNatModules_2428_; lean_object* v_natStructs_2429_; lean_object* v_natTypeIdOf_2430_; lean_object* v_exprToNatStructId_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2439_; 
v_structs_2424_ = lean_ctor_get(v_s_2423_, 0);
v_typeIdOf_2425_ = lean_ctor_get(v_s_2423_, 1);
v_exprToStructId_2426_ = lean_ctor_get(v_s_2423_, 2);
v_exprToStructIdEntries_2427_ = lean_ctor_get(v_s_2423_, 3);
v_forbiddenNatModules_2428_ = lean_ctor_get(v_s_2423_, 4);
v_natStructs_2429_ = lean_ctor_get(v_s_2423_, 5);
v_natTypeIdOf_2430_ = lean_ctor_get(v_s_2423_, 6);
v_exprToNatStructId_2431_ = lean_ctor_get(v_s_2423_, 7);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_s_2423_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2433_ = v_s_2423_;
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_exprToNatStructId_2431_);
lean_inc(v_natTypeIdOf_2430_);
lean_inc(v_natStructs_2429_);
lean_inc(v_forbiddenNatModules_2428_);
lean_inc(v_exprToStructIdEntries_2427_);
lean_inc(v_exprToStructId_2426_);
lean_inc(v_typeIdOf_2425_);
lean_inc(v_structs_2424_);
lean_dec(v_s_2423_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = lean_array_push(v_structs_2424_, v___x_2422_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2435_);
v___x_2437_ = v___x_2433_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_typeIdOf_2425_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_exprToStructId_2426_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_exprToStructIdEntries_2427_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v_forbiddenNatModules_2428_);
lean_ctor_set(v_reuseFailAlloc_2438_, 5, v_natStructs_2429_);
lean_ctor_set(v_reuseFailAlloc_2438_, 6, v_natTypeIdOf_2430_);
lean_ctor_set(v_reuseFailAlloc_2438_, 7, v_exprToNatStructId_2431_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_unsigned_to_nat(32u);
v___x_2447_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = l_Lean_mkRawNatLit(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = l_Lean_Int_mkType;
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = l_Lean_Nat_mkType;
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___y_2573_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; uint8_t v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___f_2638_; lean_object* v___x_2639_; 
lean_inc_ref_n(v_type_2560_, 2);
v___f_2638_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2638_, 0, v_type_2560_);
v___x_2639_ = l_Lean_Meta_getDecLevel_x3f(v_type_2560_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_3556_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_3556_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_3556_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
if (lean_obj_tag(v_a_2640_) == 1)
{
lean_object* v_val_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_3551_; 
lean_del_object(v___x_2642_);
v_val_2644_ = lean_ctor_get(v_a_2640_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_2646_ = v_a_2640_;
v_isShared_2647_ = v_isSharedCheck_3551_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_val_2644_);
lean_dec(v_a_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_3551_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; 
lean_inc_ref(v_type_2560_);
v___x_2648_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_3550_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_3550_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_3550_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2653_, v_val_2644_, v_type_2560_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2656_, v_val_2644_, v_type_2560_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_a_2658_, 2);
lean_dec_ref_known(v___x_2657_, 1);
lean_inc(v_a_2655_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2659_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_2658_, v_a_2655_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; uint8_t v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v_homomulFn_x3f_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_ltFn_x3f_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; uint8_t v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v_leFn_x3f_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v_charInst_x3f_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___x_3172_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
lean_inc(v_a_2655_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3172_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_2655_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
lean_inc(v_a_2655_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3174_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_2655_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
lean_inc(v_a_2655_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3176_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_2655_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; uint8_t v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___x_3383_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3383_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2563_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; uint8_t v___y_3386_; uint8_t v_ring_3471_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v_ring_3471_ = lean_ctor_get_uint8(v_a_3384_, sizeof(void*)*14 + 21);
lean_dec(v_a_3384_);
if (v_ring_3471_ == 0)
{
v___y_3386_ = v_ring_3471_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2649_, v___x_3472_);
if (v___x_3473_ == 0)
{
v___y_3386_ = v___x_3473_;
goto v___jp_3385_;
}
else
{
if (lean_obj_tag(v_a_3173_) == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v___x_3474_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3475_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3474_, v___f_2638_, v_a_2561_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3483_; 
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3475_, 0);
lean_dec(v_unused_3484_);
v___x_3477_ = v___x_3475_;
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v___x_3475_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = lean_box(0);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3479_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3475_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3475_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = 0;
v___y_3386_ = v___x_3493_;
goto v___jp_3385_;
}
}
}
v___jp_3385_:
{
lean_object* v___x_3387_; 
lean_inc(v_a_2649_);
v___x_3387_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2649_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc_n(v_a_3388_, 2);
lean_dec_ref_known(v___x_3387_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3389_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_3388_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_n(v_a_3390_, 2);
lean_dec_ref_known(v___x_3389_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_3390_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3446_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3446_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3446_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
if (lean_obj_tag(v_a_3392_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_del_object(v___x_3394_);
v_val_3396_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_val_3396_);
lean_dec_ref_known(v_a_3392_, 1);
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3397_, v_val_2644_, v_type_2560_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc_n(v_a_3399_, 2);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3401_ = lean_box(0);
lean_inc_n(v_val_2644_, 3);
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_val_2644_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
lean_inc_ref(v___x_3402_);
v___x_3403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_val_2644_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
lean_inc_ref(v___x_3403_);
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_val_2644_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
lean_inc_ref(v___x_3404_);
v___x_3405_ = l_Lean_mkConst(v___x_3400_, v___x_3404_);
lean_inc_ref_n(v_type_2560_, 3);
v___x_3406_ = l_Lean_mkApp4(v___x_3405_, v_type_2560_, v_type_2560_, v_type_2560_, v_a_3399_);
v___x_3407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3406_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3407_) == 0)
{
if (lean_obj_tag(v_a_2655_) == 1)
{
if (lean_obj_tag(v_a_3173_) == 1)
{
lean_object* v_a_3408_; lean_object* v_val_3409_; lean_object* v_val_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v_val_3409_ = lean_ctor_get(v_a_2655_, 0);
v_val_3410_ = lean_ctor_get(v_a_3173_, 0);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3402_);
v___x_3412_ = l_Lean_mkConst(v___x_3411_, v___x_3402_);
lean_inc(v_val_3410_);
lean_inc(v_val_3409_);
lean_inc(v_a_3399_);
lean_inc_ref(v_type_2560_);
v___x_3413_ = l_Lean_mkApp4(v___x_3412_, v_type_2560_, v_a_3399_, v_val_3409_, v_val_3410_);
v___x_3414_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3413_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
if (lean_obj_tag(v_a_3415_) == 0)
{
lean_dec_ref_known(v_a_3173_, 1);
v___y_3341_ = v_a_2561_;
v___y_3342_ = v_a_3415_;
v___y_3343_ = v___x_3404_;
v___y_3344_ = v___x_3402_;
v___y_3345_ = v_val_3396_;
v___y_3346_ = v_a_3388_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v_a_2570_;
v___y_3349_ = v_a_2567_;
v___y_3350_ = v_a_3399_;
v___y_3351_ = v_a_2562_;
v___y_3352_ = v_a_2566_;
v___y_3353_ = v_a_2564_;
v___y_3354_ = v_a_3390_;
v___y_3355_ = v_a_2565_;
v___y_3356_ = v_a_2569_;
v___y_3357_ = v_a_2563_;
v___y_3358_ = v___x_3403_;
v___y_3359_ = v_a_3408_;
v___y_3360_ = v_a_2568_;
goto v___jp_3340_;
}
else
{
if (v___y_3386_ == 0)
{
v___y_3287_ = v_a_2561_;
v___y_3288_ = v_a_3415_;
v___y_3289_ = v___x_3404_;
v___y_3290_ = v___x_3402_;
v___y_3291_ = v_val_3396_;
v___y_3292_ = v_a_3388_;
v___y_3293_ = v___y_3386_;
v___y_3294_ = v_a_2570_;
v___y_3295_ = v_a_2567_;
v___y_3296_ = v_a_3399_;
v___y_3297_ = v_a_2562_;
v___y_3298_ = v_a_2566_;
v___y_3299_ = v_a_2564_;
v___y_3300_ = v_a_3390_;
v___y_3301_ = v_a_2569_;
v___y_3302_ = v_a_2565_;
v___y_3303_ = v___x_3403_;
v___y_3304_ = v_a_2563_;
v___y_3305_ = v_a_2568_;
v___y_3306_ = v_a_3408_;
v___y_3307_ = v_a_3173_;
goto v___jp_3286_;
}
else
{
lean_dec_ref_known(v_a_3173_, 1);
v___y_3341_ = v_a_2561_;
v___y_3342_ = v_a_3415_;
v___y_3343_ = v___x_3404_;
v___y_3344_ = v___x_3402_;
v___y_3345_ = v_val_3396_;
v___y_3346_ = v_a_3388_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v_a_2570_;
v___y_3349_ = v_a_2567_;
v___y_3350_ = v_a_3399_;
v___y_3351_ = v_a_2562_;
v___y_3352_ = v_a_2566_;
v___y_3353_ = v_a_2564_;
v___y_3354_ = v_a_3390_;
v___y_3355_ = v_a_2565_;
v___y_3356_ = v_a_2569_;
v___y_3357_ = v_a_2563_;
v___y_3358_ = v___x_3403_;
v___y_3359_ = v_a_3408_;
v___y_3360_ = v_a_2568_;
goto v___jp_3340_;
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref_known(v_a_3173_, 1);
lean_dec(v_a_3408_);
lean_dec_ref_known(v_a_2655_, 1);
lean_dec_ref_known(v___x_3404_, 2);
lean_dec_ref_known(v___x_3403_, 2);
lean_dec_ref_known(v___x_3402_, 2);
lean_dec(v_a_3399_);
lean_dec(v_val_3396_);
lean_dec(v_a_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3416_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3414_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; 
lean_dec(v_a_3173_);
v_a_3424_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3407_, 1);
v___y_3363_ = v_a_3399_;
v___y_3364_ = v___x_3404_;
v___y_3365_ = v___x_3402_;
v___y_3366_ = v_val_3396_;
v___y_3367_ = v_a_3388_;
v___y_3368_ = v_a_3390_;
v___y_3369_ = v___y_3386_;
v___y_3370_ = v___x_3403_;
v___y_3371_ = v_a_3424_;
v___y_3372_ = v_a_2561_;
v___y_3373_ = v_a_2562_;
v___y_3374_ = v_a_2563_;
v___y_3375_ = v_a_2564_;
v___y_3376_ = v_a_2565_;
v___y_3377_ = v_a_2566_;
v___y_3378_ = v_a_2567_;
v___y_3379_ = v_a_2568_;
v___y_3380_ = v_a_2569_;
v___y_3381_ = v_a_2570_;
goto v___jp_3362_;
}
}
else
{
lean_object* v_a_3425_; 
lean_dec(v_a_3173_);
v_a_3425_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3407_, 1);
v___y_3363_ = v_a_3399_;
v___y_3364_ = v___x_3404_;
v___y_3365_ = v___x_3402_;
v___y_3366_ = v_val_3396_;
v___y_3367_ = v_a_3388_;
v___y_3368_ = v_a_3390_;
v___y_3369_ = v___y_3386_;
v___y_3370_ = v___x_3403_;
v___y_3371_ = v_a_3425_;
v___y_3372_ = v_a_2561_;
v___y_3373_ = v_a_2562_;
v___y_3374_ = v_a_2563_;
v___y_3375_ = v_a_2564_;
v___y_3376_ = v_a_2565_;
v___y_3377_ = v_a_2566_;
v___y_3378_ = v_a_2567_;
v___y_3379_ = v_a_2568_;
v___y_3380_ = v_a_2569_;
v___y_3381_ = v_a_2570_;
goto v___jp_3362_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref_known(v___x_3404_, 2);
lean_dec_ref_known(v___x_3403_, 2);
lean_dec_ref_known(v___x_3402_, 2);
lean_dec(v_a_3399_);
lean_dec(v_val_3396_);
lean_dec(v_a_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3426_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3407_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3407_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v_val_3396_);
lean_dec(v_a_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3434_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3398_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3398_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v___x_3442_ = lean_box(0);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v___x_3442_);
v___x_3444_ = v___x_3394_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_a_3390_);
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3447_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3391_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3391_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v_a_3388_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3455_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3389_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3389_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3463_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3387_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3387_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3494_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3383_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3383_);
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
v___jp_3178_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc(v___y_3186_);
lean_inc(v_a_2655_);
v___x_3201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2655_, v___y_3186_, v_a_3175_, v___x_3200_, v_val_2644_, v_type_2560_, v___y_3193_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v___x_3203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc(v_a_2655_);
v___x_3204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2655_, v_a_3202_, v_a_3177_, v___x_3203_, v_val_2644_, v_type_2560_, v___y_3193_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3182_, 2);
v___x_3210_ = l_Lean_mkConst(v___x_3209_, v___y_3182_);
lean_inc_ref(v___y_3183_);
lean_inc_ref_n(v_type_2560_, 3);
v___x_3211_ = l_Lean_mkAppB(v___x_3210_, v_type_2560_, v___y_3183_);
v___x_3212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3214_ = l_Lean_mkConst(v___x_3213_, v___y_3182_);
lean_inc_ref(v___x_3211_);
v___x_3215_ = l_Lean_mkAppB(v___x_3214_, v_type_2560_, v___x_3211_);
lean_inc(v___y_3192_);
lean_inc(v_val_2644_);
v___x_3216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2644_, v_type_2560_, v___y_3192_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3219_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3218_, v_val_2644_, v_type_2560_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2644_, v_type_2560_, v___y_3179_, v___y_3189_, v___y_3196_, v___y_3191_, v___y_3193_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
lean_inc(v___y_3186_);
lean_inc(v_a_2658_);
lean_inc(v_a_2655_);
lean_inc(v_a_3217_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2644_, v_type_2560_, v_a_3217_, v_a_2655_, v_a_2658_, v___y_3186_, v___y_3193_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3223_) == 0)
{
if (lean_obj_tag(v_a_3217_) == 1)
{
lean_object* v_a_3224_; lean_object* v_val_3225_; lean_object* v___x_3226_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_val_3225_ = lean_ctor_get(v_a_3217_, 0);
lean_inc(v_val_3225_);
lean_dec_ref_known(v_a_3217_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_3226_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2644_, v_type_2560_, v_val_3225_, v___y_3179_, v___y_3189_, v___y_3196_, v___y_3191_, v___y_3193_, v___y_3190_, v___y_3187_, v___y_3198_, v___y_3194_, v___y_3185_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___y_2870_ = v_a_3224_;
v___y_2871_ = v___x_3208_;
v___y_2872_ = v___y_3181_;
v___y_2873_ = v___y_3180_;
v___y_2874_ = v___y_3182_;
v___y_2875_ = v___y_3183_;
v___y_2876_ = v___y_3184_;
v___y_2877_ = v___x_3212_;
v___y_2878_ = v___y_3186_;
v___y_2879_ = v___x_3215_;
v___y_2880_ = v_a_3222_;
v___y_2881_ = v___y_3188_;
v___y_2882_ = v___x_3206_;
v___y_2883_ = v___y_3199_;
v___y_2884_ = v_a_3205_;
v___y_2885_ = v___x_3207_;
v___y_2886_ = v_a_3220_;
v___y_2887_ = v___y_3192_;
v___y_2888_ = v___x_3211_;
v___y_2889_ = v___y_3195_;
v___y_2890_ = v___y_3197_;
v_charInst_x3f_2891_ = v_a_3227_;
v___y_2892_ = v___y_3179_;
v___y_2893_ = v___y_3189_;
v___y_2894_ = v___y_3196_;
v___y_2895_ = v___y_3191_;
v___y_2896_ = v___y_3193_;
v___y_2897_ = v___y_3190_;
v___y_2898_ = v___y_3187_;
v___y_2899_ = v___y_3198_;
v___y_2900_ = v___y_3194_;
v___y_2901_ = v___y_3185_;
goto v___jp_2869_;
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v_a_3224_);
lean_dec(v_a_3222_);
lean_dec(v_a_3220_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3211_);
lean_dec(v_a_3205_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3228_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3226_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3226_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3237_; 
lean_dec(v_a_3217_);
v_a_3236_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3237_ = lean_box(0);
v___y_2870_ = v_a_3236_;
v___y_2871_ = v___x_3208_;
v___y_2872_ = v___y_3181_;
v___y_2873_ = v___y_3180_;
v___y_2874_ = v___y_3182_;
v___y_2875_ = v___y_3183_;
v___y_2876_ = v___y_3184_;
v___y_2877_ = v___x_3212_;
v___y_2878_ = v___y_3186_;
v___y_2879_ = v___x_3215_;
v___y_2880_ = v_a_3222_;
v___y_2881_ = v___y_3188_;
v___y_2882_ = v___x_3206_;
v___y_2883_ = v___y_3199_;
v___y_2884_ = v_a_3205_;
v___y_2885_ = v___x_3207_;
v___y_2886_ = v_a_3220_;
v___y_2887_ = v___y_3192_;
v___y_2888_ = v___x_3211_;
v___y_2889_ = v___y_3195_;
v___y_2890_ = v___y_3197_;
v_charInst_x3f_2891_ = v___x_3237_;
v___y_2892_ = v___y_3179_;
v___y_2893_ = v___y_3189_;
v___y_2894_ = v___y_3196_;
v___y_2895_ = v___y_3191_;
v___y_2896_ = v___y_3193_;
v___y_2897_ = v___y_3190_;
v___y_2898_ = v___y_3187_;
v___y_2899_ = v___y_3198_;
v___y_2900_ = v___y_3194_;
v___y_2901_ = v___y_3185_;
goto v___jp_2869_;
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v_a_3222_);
lean_dec(v_a_3220_);
lean_dec(v_a_3217_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3211_);
lean_dec(v_a_3205_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3238_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3223_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3223_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_a_3220_);
lean_dec(v_a_3217_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3211_);
lean_dec(v_a_3205_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3246_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3221_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3221_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_a_3217_);
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3211_);
lean_dec(v_a_3205_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3254_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3219_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3219_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v___x_3215_);
lean_dec_ref(v___x_3211_);
lean_dec(v_a_3205_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3262_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3216_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3216_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3270_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3204_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3204_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3186_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v_a_3177_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3278_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3201_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3201_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
v___jp_3286_:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3304_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; uint8_t v_ring_3310_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v_ring_3310_ = lean_ctor_get_uint8(v_a_3309_, sizeof(void*)*14 + 21);
lean_dec(v_a_3309_);
if (v_ring_3310_ == 0)
{
lean_dec_ref(v___f_2638_);
v___y_3179_ = v___y_3287_;
v___y_3180_ = v___y_3288_;
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3294_;
v___y_3186_ = v___y_3307_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3296_;
v___y_3189_ = v___y_3297_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3302_;
v___y_3194_ = v___y_3301_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v_ring_3310_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_box(0);
v___x_3312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2649_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_dec_ref(v___f_2638_);
v___y_3179_ = v___y_3287_;
v___y_3180_ = v___y_3288_;
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3294_;
v___y_3186_ = v___y_3307_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3296_;
v___y_3189_ = v___y_3297_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3302_;
v___y_3194_ = v___y_3301_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v___x_3312_;
goto v___jp_3178_;
}
else
{
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3303_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v___x_3313_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3314_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3313_, v___f_2638_, v___y_3287_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v___x_3314_, 0);
lean_dec(v_unused_3323_);
v___x_3316_ = v___x_3314_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_dec(v___x_3314_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3318_);
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3314_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3314_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_dec_ref(v___f_2638_);
v___y_3179_ = v___y_3287_;
v___y_3180_ = v___y_3288_;
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3294_;
v___y_3186_ = v___y_3307_;
v___y_3187_ = v___y_3295_;
v___y_3188_ = v___y_3296_;
v___y_3189_ = v___y_3297_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3302_;
v___y_3194_ = v___y_3301_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v___y_3293_;
goto v___jp_3178_;
}
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3303_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3332_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3308_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3308_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
v___jp_3340_:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_box(0);
v___y_3287_ = v___y_3341_;
v___y_3288_ = v___y_3342_;
v___y_3289_ = v___y_3343_;
v___y_3290_ = v___y_3344_;
v___y_3291_ = v___y_3345_;
v___y_3292_ = v___y_3346_;
v___y_3293_ = v___y_3347_;
v___y_3294_ = v___y_3348_;
v___y_3295_ = v___y_3349_;
v___y_3296_ = v___y_3350_;
v___y_3297_ = v___y_3351_;
v___y_3298_ = v___y_3352_;
v___y_3299_ = v___y_3353_;
v___y_3300_ = v___y_3354_;
v___y_3301_ = v___y_3356_;
v___y_3302_ = v___y_3355_;
v___y_3303_ = v___y_3358_;
v___y_3304_ = v___y_3357_;
v___y_3305_ = v___y_3360_;
v___y_3306_ = v___y_3359_;
v___y_3307_ = v___x_3361_;
goto v___jp_3286_;
}
v___jp_3362_:
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_box(0);
v___y_3341_ = v___y_3372_;
v___y_3342_ = v___x_3382_;
v___y_3343_ = v___y_3364_;
v___y_3344_ = v___y_3365_;
v___y_3345_ = v___y_3366_;
v___y_3346_ = v___y_3367_;
v___y_3347_ = v___y_3369_;
v___y_3348_ = v___y_3381_;
v___y_3349_ = v___y_3378_;
v___y_3350_ = v___y_3363_;
v___y_3351_ = v___y_3373_;
v___y_3352_ = v___y_3377_;
v___y_3353_ = v___y_3375_;
v___y_3354_ = v___y_3368_;
v___y_3355_ = v___y_3376_;
v___y_3356_ = v___y_3380_;
v___y_3357_ = v___y_3374_;
v___y_3358_ = v___y_3370_;
v___y_3359_ = v___y_3371_;
v___y_3360_ = v___y_3379_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec(v_a_3175_);
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3502_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3176_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3176_);
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
lean_dec(v_a_3173_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3510_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3174_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3174_);
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
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3518_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3172_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3172_);
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
v___jp_2661_:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2687_, v___y_2695_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v_structs_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v_structs_2699_ = lean_ctor_get(v_a_2698_, 0);
lean_inc_ref(v_structs_2699_);
lean_dec(v_a_2698_);
v___x_2700_ = lean_array_get_size(v_structs_2699_);
lean_dec_ref(v_structs_2699_);
v___x_2701_ = lean_unsigned_to_nat(32u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2704_ = ((size_t)5ULL);
lean_inc(v___y_2676_);
v___x_2705_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2702_);
lean_ctor_set(v___x_2705_, 2, v___y_2676_);
lean_ctor_set(v___x_2705_, 3, v___y_2676_);
lean_ctor_set_usize(v___x_2705_, 4, v___x_2704_);
v___x_2706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_box(0);
lean_inc_ref_n(v___x_2705_, 7);
lean_inc(v___y_2672_);
lean_inc(v___y_2667_);
lean_inc(v___y_2677_);
lean_inc(v___y_2665_);
lean_inc(v___y_2679_);
v___x_2709_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2700_);
lean_ctor_set(v___x_2709_, 1, v_a_2649_);
lean_ctor_set(v___x_2709_, 2, v_type_2560_);
lean_ctor_set(v___x_2709_, 3, v_val_2644_);
lean_ctor_set(v___x_2709_, 4, v___y_2668_);
lean_ctor_set(v___x_2709_, 5, v_a_2655_);
lean_ctor_set(v___x_2709_, 6, v_a_2658_);
lean_ctor_set(v___x_2709_, 7, v_a_2660_);
lean_ctor_set(v___x_2709_, 8, v___y_2671_);
lean_ctor_set(v___x_2709_, 9, v___y_2666_);
lean_ctor_set(v___x_2709_, 10, v___y_2675_);
lean_ctor_set(v___x_2709_, 11, v___y_2670_);
lean_ctor_set(v___x_2709_, 12, v___y_2679_);
lean_ctor_set(v___x_2709_, 13, v___y_2669_);
lean_ctor_set(v___x_2709_, 14, v___y_2665_);
lean_ctor_set(v___x_2709_, 15, v___y_2677_);
lean_ctor_set(v___x_2709_, 16, v___y_2667_);
lean_ctor_set(v___x_2709_, 17, v___y_2680_);
lean_ctor_set(v___x_2709_, 18, v___y_2681_);
lean_ctor_set(v___x_2709_, 19, v___y_2672_);
lean_ctor_set(v___x_2709_, 20, v___y_2682_);
lean_ctor_set(v___x_2709_, 21, v___y_2685_);
lean_ctor_set(v___x_2709_, 22, v___y_2684_);
lean_ctor_set(v___x_2709_, 23, v___y_2664_);
lean_ctor_set(v___x_2709_, 24, v___y_2663_);
lean_ctor_set(v___x_2709_, 25, v___y_2674_);
lean_ctor_set(v___x_2709_, 26, v___y_2662_);
lean_ctor_set(v___x_2709_, 27, v_homomulFn_x3f_2686_);
lean_ctor_set(v___x_2709_, 28, v___y_2678_);
lean_ctor_set(v___x_2709_, 29, v___y_2683_);
lean_ctor_set(v___x_2709_, 30, v___x_2705_);
lean_ctor_set(v___x_2709_, 31, v___x_2706_);
lean_ctor_set(v___x_2709_, 32, v___x_2705_);
lean_ctor_set(v___x_2709_, 33, v___x_2705_);
lean_ctor_set(v___x_2709_, 34, v___x_2705_);
lean_ctor_set(v___x_2709_, 35, v___x_2705_);
lean_ctor_set(v___x_2709_, 36, v___x_2707_);
lean_ctor_set(v___x_2709_, 37, v___x_2706_);
lean_ctor_set(v___x_2709_, 38, v___x_2705_);
lean_ctor_set(v___x_2709_, 39, v___x_2708_);
lean_ctor_set(v___x_2709_, 40, v___x_2705_);
lean_ctor_set(v___x_2709_, 41, v___x_2705_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*42, v___y_2673_);
v___f_2710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_2710_, 0, v___x_2709_);
v___x_2711_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2712_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2711_, v___f_2710_, v___y_2687_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_dec_ref_known(v___x_2712_, 1);
if (lean_obj_tag(v___y_2672_) == 1)
{
if (lean_obj_tag(v___y_2679_) == 0)
{
lean_dec_ref_known(v___y_2672_, 1);
lean_dec(v___y_2677_);
lean_dec(v___y_2667_);
lean_dec(v___y_2665_);
v___y_2573_ = v___x_2700_;
goto v___jp_2572_;
}
else
{
lean_dec_ref_known(v___y_2679_, 1);
if (lean_obj_tag(v___y_2665_) == 0)
{
if (v___y_2673_ == 0)
{
if (lean_obj_tag(v___y_2677_) == 0)
{
lean_object* v_val_2713_; uint8_t v___x_2714_; 
v_val_2713_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v___y_2672_, 1);
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2667_);
lean_dec(v___y_2667_);
if (v___x_2714_ == 0)
{
lean_dec(v_val_2713_);
v___y_2573_ = v___x_2700_;
goto v___jp_2572_;
}
else
{
v___y_2614_ = v___y_2691_;
v___y_2615_ = v_val_2713_;
v___y_2616_ = v___y_2692_;
v___y_2617_ = v___y_2693_;
v___y_2618_ = v___y_2689_;
v___y_2619_ = v___y_2696_;
v___y_2620_ = v___y_2673_;
v___y_2621_ = v___x_2700_;
v___y_2622_ = v___y_2688_;
v___y_2623_ = v___y_2690_;
v___y_2624_ = v___y_2694_;
v___y_2625_ = v___y_2687_;
v___y_2626_ = v___y_2695_;
goto v___jp_2613_;
}
}
else
{
lean_object* v_val_2715_; 
lean_dec_ref_known(v___y_2677_, 1);
lean_dec(v___y_2667_);
v_val_2715_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v___y_2672_, 1);
v___y_2614_ = v___y_2691_;
v___y_2615_ = v_val_2715_;
v___y_2616_ = v___y_2692_;
v___y_2617_ = v___y_2693_;
v___y_2618_ = v___y_2689_;
v___y_2619_ = v___y_2696_;
v___y_2620_ = v___y_2673_;
v___y_2621_ = v___x_2700_;
v___y_2622_ = v___y_2688_;
v___y_2623_ = v___y_2690_;
v___y_2624_ = v___y_2694_;
v___y_2625_ = v___y_2687_;
v___y_2626_ = v___y_2695_;
goto v___jp_2613_;
}
}
else
{
lean_object* v_val_2716_; 
lean_dec(v___y_2677_);
lean_dec(v___y_2667_);
v_val_2716_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v___y_2672_, 1);
v___y_2588_ = v___y_2691_;
v___y_2589_ = v_val_2716_;
v___y_2590_ = v___y_2692_;
v___y_2591_ = v___y_2693_;
v___y_2592_ = v___y_2689_;
v___y_2593_ = v___y_2696_;
v___y_2594_ = v___y_2673_;
v___y_2595_ = v___x_2700_;
v___y_2596_ = v___y_2688_;
v___y_2597_ = v___y_2690_;
v___y_2598_ = v___y_2694_;
v___y_2599_ = v___y_2687_;
v___y_2600_ = v___y_2695_;
goto v___jp_2587_;
}
}
else
{
lean_object* v_val_2717_; 
lean_dec_ref_known(v___y_2665_, 1);
lean_dec(v___y_2677_);
lean_dec(v___y_2667_);
v_val_2717_ = lean_ctor_get(v___y_2672_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v___y_2672_, 1);
v___y_2588_ = v___y_2691_;
v___y_2589_ = v_val_2717_;
v___y_2590_ = v___y_2692_;
v___y_2591_ = v___y_2693_;
v___y_2592_ = v___y_2689_;
v___y_2593_ = v___y_2696_;
v___y_2594_ = v___y_2673_;
v___y_2595_ = v___x_2700_;
v___y_2596_ = v___y_2688_;
v___y_2597_ = v___y_2690_;
v___y_2598_ = v___y_2694_;
v___y_2599_ = v___y_2687_;
v___y_2600_ = v___y_2695_;
goto v___jp_2587_;
}
}
}
else
{
lean_dec(v___y_2679_);
lean_dec(v___y_2677_);
lean_dec(v___y_2672_);
lean_dec(v___y_2667_);
lean_dec(v___y_2665_);
v___y_2573_ = v___x_2700_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v___y_2679_);
lean_dec(v___y_2677_);
lean_dec(v___y_2672_);
lean_dec(v___y_2667_);
lean_dec(v___y_2665_);
v_a_2718_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2712_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2712_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_homomulFn_x3f_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_dec(v_a_2649_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2726_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2697_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2697_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
v___jp_2734_:
{
lean_object* v___x_2769_; 
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2644_, v_type_2560_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2644_, v_type_2560_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2771_) == 0)
{
if (lean_obj_tag(v___y_2742_) == 0)
{
lean_object* v_a_2772_; 
lean_dec(v___y_2738_);
lean_del_object(v___x_2646_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___y_2662_ = v_a_2772_;
v___y_2663_ = v___y_2735_;
v___y_2664_ = v___y_2736_;
v___y_2665_ = v___y_2737_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2744_;
v___y_2671_ = v___y_2745_;
v___y_2672_ = v___y_2746_;
v___y_2673_ = v___y_2747_;
v___y_2674_ = v_a_2770_;
v___y_2675_ = v___y_2748_;
v___y_2676_ = v___y_2749_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2752_;
v___y_2679_ = v___y_2751_;
v___y_2680_ = v___y_2754_;
v___y_2681_ = v___y_2753_;
v___y_2682_ = v___y_2755_;
v___y_2683_ = v___y_2756_;
v___y_2684_ = v___y_2757_;
v___y_2685_ = v_ltFn_x3f_2758_;
v_homomulFn_x3f_2686_ = v___y_2743_;
v___y_2687_ = v___y_2759_;
v___y_2688_ = v___y_2760_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2766_;
v___y_2695_ = v___y_2767_;
v___y_2696_ = v___y_2768_;
goto v___jp_2661_;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v___y_2743_);
v_a_2773_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2774_, v_val_2644_, v_type_2560_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2778_ = l_Lean_mkConst(v___x_2777_, v___y_2738_);
lean_inc_ref_n(v_type_2560_, 3);
v___x_2779_ = l_Lean_mkApp4(v___x_2778_, v_type_2560_, v_type_2560_, v_type_2560_, v_a_2776_);
v___x_2780_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2779_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v_a_2781_);
v___x_2783_ = v___x_2646_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v___y_2662_ = v_a_2773_;
v___y_2663_ = v___y_2735_;
v___y_2664_ = v___y_2736_;
v___y_2665_ = v___y_2737_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2744_;
v___y_2671_ = v___y_2745_;
v___y_2672_ = v___y_2746_;
v___y_2673_ = v___y_2747_;
v___y_2674_ = v_a_2770_;
v___y_2675_ = v___y_2748_;
v___y_2676_ = v___y_2749_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2752_;
v___y_2679_ = v___y_2751_;
v___y_2680_ = v___y_2754_;
v___y_2681_ = v___y_2753_;
v___y_2682_ = v___y_2755_;
v___y_2683_ = v___y_2756_;
v___y_2684_ = v___y_2757_;
v___y_2685_ = v_ltFn_x3f_2758_;
v_homomulFn_x3f_2686_ = v___x_2783_;
v___y_2687_ = v___y_2759_;
v___y_2688_ = v___y_2760_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2766_;
v___y_2695_ = v___y_2767_;
v___y_2696_ = v___y_2768_;
goto v___jp_2661_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref_known(v___y_2742_, 1);
lean_dec(v_a_2773_);
lean_dec(v_a_2770_);
lean_dec(v_ltFn_x3f_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2785_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2780_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2780_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec_ref_known(v___y_2742_, 1);
lean_dec(v_a_2773_);
lean_dec(v_a_2770_);
lean_dec(v_ltFn_x3f_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2793_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2775_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2775_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2770_);
lean_dec(v_ltFn_x3f_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2801_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2771_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2771_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_ltFn_x3f_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2809_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2769_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2769_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
v___jp_2817_:
{
if (lean_obj_tag(v_a_2658_) == 1)
{
lean_object* v_val_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_val_2852_ = lean_ctor_get(v_a_2658_, 0);
v___x_2853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2854_ = l_Lean_mkConst(v___x_2853_, v___y_2824_);
lean_inc(v_val_2852_);
lean_inc_ref(v_type_2560_);
v___x_2855_ = l_Lean_mkAppB(v___x_2854_, v_type_2560_, v_val_2852_);
v___x_2856_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2855_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 1);
lean_ctor_set(v___x_2651_, 0, v_a_2857_);
v___x_2859_ = v___x_2651_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
v___y_2735_ = v___y_2818_;
v___y_2736_ = v___y_2819_;
v___y_2737_ = v___y_2820_;
v___y_2738_ = v___y_2821_;
v___y_2739_ = v___y_2822_;
v___y_2740_ = v___y_2823_;
v___y_2741_ = v___y_2825_;
v___y_2742_ = v___y_2826_;
v___y_2743_ = v___y_2827_;
v___y_2744_ = v___y_2828_;
v___y_2745_ = v___y_2829_;
v___y_2746_ = v___y_2830_;
v___y_2747_ = v___y_2831_;
v___y_2748_ = v___y_2832_;
v___y_2749_ = v___y_2833_;
v___y_2750_ = v___y_2834_;
v___y_2751_ = v___y_2836_;
v___y_2752_ = v___y_2835_;
v___y_2753_ = v___y_2838_;
v___y_2754_ = v___y_2837_;
v___y_2755_ = v_leFn_x3f_2841_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2840_;
v_ltFn_x3f_2758_ = v___x_2859_;
v___y_2759_ = v___y_2842_;
v___y_2760_ = v___y_2843_;
v___y_2761_ = v___y_2844_;
v___y_2762_ = v___y_2845_;
v___y_2763_ = v___y_2846_;
v___y_2764_ = v___y_2847_;
v___y_2765_ = v___y_2848_;
v___y_2766_ = v___y_2849_;
v___y_2767_ = v___y_2850_;
v___y_2768_ = v___y_2851_;
goto v___jp_2734_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref_known(v_a_2658_, 1);
lean_dec(v_leFn_x3f_2841_);
lean_dec_ref(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v_a_2660_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2861_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2856_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2856_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_dec(v___y_2824_);
lean_del_object(v___x_2651_);
lean_inc(v___y_2827_);
v___y_2735_ = v___y_2818_;
v___y_2736_ = v___y_2819_;
v___y_2737_ = v___y_2820_;
v___y_2738_ = v___y_2821_;
v___y_2739_ = v___y_2822_;
v___y_2740_ = v___y_2823_;
v___y_2741_ = v___y_2825_;
v___y_2742_ = v___y_2826_;
v___y_2743_ = v___y_2827_;
v___y_2744_ = v___y_2828_;
v___y_2745_ = v___y_2829_;
v___y_2746_ = v___y_2830_;
v___y_2747_ = v___y_2831_;
v___y_2748_ = v___y_2832_;
v___y_2749_ = v___y_2833_;
v___y_2750_ = v___y_2834_;
v___y_2751_ = v___y_2836_;
v___y_2752_ = v___y_2835_;
v___y_2753_ = v___y_2838_;
v___y_2754_ = v___y_2837_;
v___y_2755_ = v_leFn_x3f_2841_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2840_;
v_ltFn_x3f_2758_ = v___y_2827_;
v___y_2759_ = v___y_2842_;
v___y_2760_ = v___y_2843_;
v___y_2761_ = v___y_2844_;
v___y_2762_ = v___y_2845_;
v___y_2763_ = v___y_2846_;
v___y_2764_ = v___y_2847_;
v___y_2765_ = v___y_2848_;
v___y_2766_ = v___y_2849_;
v___y_2767_ = v___y_2850_;
v___y_2768_ = v___y_2851_;
goto v___jp_2734_;
}
}
v___jp_2869_:
{
lean_object* v___x_2902_; 
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2902_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2644_, v_type_2560_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2905_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2904_, v_val_2644_, v_type_2560_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_n(v_a_2906_, 2);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2874_);
v___x_2908_ = l_Lean_mkConst(v___x_2907_, v___y_2874_);
lean_inc_ref(v_type_2560_);
v___x_2909_ = l_Lean_mkAppB(v___x_2908_, v_type_2560_, v_a_2906_);
v___x_2910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2909_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2874_);
v___x_2913_ = l_Lean_mkConst(v___x_2912_, v___y_2874_);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2560_);
v___x_2916_ = l_Lean_mkAppB(v___x_2913_, v_type_2560_, v___x_2915_);
v___x_2917_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2916_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_3139_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_3139_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_3139_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_val_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_2920_);
v_val_2922_ = lean_ctor_get(v_a_2918_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_2918_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_2924_ = v_a_2918_;
v_isShared_2925_ = v_isSharedCheck_3134_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_val_2922_);
lean_dec(v_a_2918_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_3134_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2874_);
v___x_2927_ = l_Lean_mkConst(v___x_2926_, v___y_2874_);
lean_inc_ref(v_type_2560_);
v___x_2928_ = l_Lean_mkApp3(v___x_2927_, v_type_2560_, v___x_2915_, v_val_2922_);
v___x_2929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2928_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc_n(v_a_2930_, 2);
lean_dec_ref_known(v___x_2929_, 1);
lean_inc(v_a_2911_);
v___x_2931_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2911_, v_a_2930_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec_ref_known(v___x_2931_, 1);
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2932_, v_val_2644_, v_type_2560_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc_n(v_a_2934_, 2);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2872_);
v___x_2936_ = l_Lean_mkConst(v___x_2935_, v___y_2872_);
lean_inc_ref_n(v_type_2560_, 3);
v___x_2937_ = l_Lean_mkApp4(v___x_2936_, v_type_2560_, v_type_2560_, v_type_2560_, v_a_2934_);
v___x_2938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2937_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2940_, v_val_2644_, v_type_2560_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_n(v_a_2942_, 2);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2874_);
v___x_2944_ = l_Lean_mkConst(v___x_2943_, v___y_2874_);
lean_inc_ref(v_type_2560_);
v___x_2945_ = l_Lean_mkAppB(v___x_2944_, v_type_2560_, v_a_2942_);
v___x_2946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2945_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2644_, v_type_2560_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_n(v_a_2949_, 2);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___y_2889_);
v___x_2953_ = l_Lean_mkConst(v___x_2950_, v___x_2952_);
v___x_2954_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2560_, 2);
lean_inc_ref(v___x_2953_);
v___x_2955_ = l_Lean_mkApp4(v___x_2953_, v___x_2954_, v_type_2560_, v_type_2560_, v_a_2949_);
v___x_2956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2955_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2644_, v_type_2560_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc_n(v_a_2959_, 2);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2560_, 2);
v___x_2961_ = l_Lean_mkApp4(v___x_2953_, v___x_2960_, v_type_2560_, v_type_2560_, v_a_2959_);
v___x_2962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2961_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2966_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___x_2964_, v___x_2965_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc_ref(v___y_2879_);
v___x_2967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2906_, v___y_2879_, v___x_2966_, v_val_2644_, v_type_2560_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2969_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___x_2964_, v___x_2968_);
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_2971_ = lean_box(0);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2881_, v___y_2879_, v___x_2969_, v___x_2970_, v_val_2644_, v_type_2560_, v___x_2971_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec_ref_known(v___x_2972_, 1);
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2877_);
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2974_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___y_2877_, v___x_2973_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc_ref(v___y_2888_);
v___x_2976_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2934_, v___y_2888_, v___x_2974_, v___x_2975_, v_val_2644_, v_type_2560_, v___x_2971_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref_known(v___x_2976_, 1);
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2877_);
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2978_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___y_2877_, v___x_2977_);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2942_, v___y_2888_, v___x_2978_, v_val_2644_, v_type_2560_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec_ref_known(v___x_2979_, 1);
v___x_2980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2871_);
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2981_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___y_2871_, v___x_2980_);
v___x_2982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_2983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc_ref(v___y_2875_);
v___x_2984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2949_, v___y_2875_, v___x_2981_, v___x_2982_, v_val_2644_, v_type_2560_, v___x_2983_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_dec_ref_known(v___x_2984_, 1);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2871_);
lean_inc_ref(v___y_2885_);
lean_inc_ref(v___y_2882_);
v___x_2986_ = l_Lean_Name_mkStr4(v___y_2882_, v___y_2885_, v___y_2871_, v___x_2985_);
v___x_2987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2560_);
lean_inc(v_val_2644_);
lean_inc_ref(v___y_2875_);
v___x_2988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2959_, v___y_2875_, v___x_2986_, v___x_2982_, v_val_2644_, v_type_2560_, v___x_2987_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
if (lean_obj_tag(v_a_2655_) == 1)
{
lean_object* v_val_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_val_2989_ = lean_ctor_get(v_a_2655_, 0);
v___x_2990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2874_);
v___x_2991_ = l_Lean_mkConst(v___x_2990_, v___y_2874_);
lean_inc(v_val_2989_);
lean_inc_ref(v_type_2560_);
v___x_2992_ = l_Lean_mkAppB(v___x_2991_, v_type_2560_, v_val_2989_);
v___x_2993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2992_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v_a_2994_);
v___x_2996_ = v___x_2924_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
v___y_2818_ = v_a_2963_;
v___y_2819_ = v_a_2957_;
v___y_2820_ = v___y_2870_;
v___y_2821_ = v___y_2872_;
v___y_2822_ = v___y_2873_;
v___y_2823_ = v_charInst_x3f_2891_;
v___y_2824_ = v___y_2874_;
v___y_2825_ = v___y_2875_;
v___y_2826_ = v___y_2876_;
v___y_2827_ = v___x_2971_;
v___y_2828_ = v_a_2903_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2880_;
v___y_2831_ = v___y_2883_;
v___y_2832_ = v___y_2884_;
v___y_2833_ = v___x_2914_;
v___y_2834_ = v___y_2886_;
v___y_2835_ = v_a_2939_;
v___y_2836_ = v___y_2887_;
v___y_2837_ = v_a_2911_;
v___y_2838_ = v_a_2930_;
v___y_2839_ = v_a_2947_;
v___y_2840_ = v___y_2890_;
v_leFn_x3f_2841_ = v___x_2996_;
v___y_2842_ = v___y_2892_;
v___y_2843_ = v___y_2893_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v___y_2895_;
v___y_2846_ = v___y_2896_;
v___y_2847_ = v___y_2897_;
v___y_2848_ = v___y_2898_;
v___y_2849_ = v___y_2899_;
v___y_2850_ = v___y_2900_;
v___y_2851_ = v___y_2901_;
goto v___jp_2817_;
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref_known(v_a_2655_, 1);
lean_dec(v_a_2963_);
lean_dec(v_a_2957_);
lean_dec(v_a_2947_);
lean_dec(v_a_2939_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_2998_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2993_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2993_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_del_object(v___x_2924_);
v___y_2818_ = v_a_2963_;
v___y_2819_ = v_a_2957_;
v___y_2820_ = v___y_2870_;
v___y_2821_ = v___y_2872_;
v___y_2822_ = v___y_2873_;
v___y_2823_ = v_charInst_x3f_2891_;
v___y_2824_ = v___y_2874_;
v___y_2825_ = v___y_2875_;
v___y_2826_ = v___y_2876_;
v___y_2827_ = v___x_2971_;
v___y_2828_ = v_a_2903_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2880_;
v___y_2831_ = v___y_2883_;
v___y_2832_ = v___y_2884_;
v___y_2833_ = v___x_2914_;
v___y_2834_ = v___y_2886_;
v___y_2835_ = v_a_2939_;
v___y_2836_ = v___y_2887_;
v___y_2837_ = v_a_2911_;
v___y_2838_ = v_a_2930_;
v___y_2839_ = v_a_2947_;
v___y_2840_ = v___y_2890_;
v_leFn_x3f_2841_ = v___x_2971_;
v___y_2842_ = v___y_2892_;
v___y_2843_ = v___y_2893_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v___y_2895_;
v___y_2846_ = v___y_2896_;
v___y_2847_ = v___y_2897_;
v___y_2848_ = v___y_2898_;
v___y_2849_ = v___y_2899_;
v___y_2850_ = v___y_2900_;
v___y_2851_ = v___y_2901_;
goto v___jp_2817_;
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2957_);
lean_dec(v_a_2947_);
lean_dec(v_a_2939_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3006_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2988_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2988_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2947_);
lean_dec(v_a_2939_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3014_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2984_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2984_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2939_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3022_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2979_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2979_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3030_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2976_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2976_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3038_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2972_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2972_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3046_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_2967_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_2967_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v_a_2959_);
lean_dec(v_a_2957_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3054_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2962_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2962_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_a_2957_);
lean_dec_ref(v___x_2953_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3062_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2958_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2958_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v___x_2953_);
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3070_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2956_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2956_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_2947_);
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3078_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2948_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2948_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_2942_);
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3086_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_2946_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_2946_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_a_2939_);
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3094_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_2941_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_2941_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_2934_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3102_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_2938_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_2938_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3110_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_2933_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_2933_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_2930_);
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3118_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2931_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_2931_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_del_object(v___x_2924_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3126_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_2929_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_2929_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
lean_dec(v_a_2918_);
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v___x_3135_ = lean_box(0);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v___x_3135_);
v___x_3137_ = v___x_2920_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_a_2911_);
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3140_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_2917_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_2917_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_2906_);
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3148_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_2910_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_2910_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_a_2903_);
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3156_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_2905_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_2905_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_charInst_x3f_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec(v___y_2870_);
lean_dec(v_a_2660_);
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v_type_2560_);
v_a_3164_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_2902_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_2902_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_2658_);
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3526_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_2659_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_2659_);
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
lean_dec(v_a_2655_);
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3534_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_2657_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_2657_);
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
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_2651_);
lean_dec(v_a_2649_);
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3542_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_2654_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_2654_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
else
{
lean_del_object(v___x_2646_);
lean_dec(v_val_2644_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
return v___x_2648_;
}
}
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
lean_dec(v_a_2640_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v___x_3552_ = lean_box(0);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_3552_);
v___x_3554_ = v___x_2642_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v___f_2638_);
lean_dec_ref(v_type_2560_);
v_a_3557_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_2639_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_2639_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
v___jp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___y_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
v___jp_2576_:
{
if (lean_obj_tag(v___y_2578_) == 0)
{
lean_dec_ref_known(v___y_2578_, 1);
v___y_2573_ = v___y_2577_;
goto v___jp_2572_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v___y_2577_);
v_a_2579_ = lean_ctor_get(v___y_2578_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___y_2578_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___y_2578_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___y_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
v___jp_2587_:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2589_, v___y_2594_, v___y_2595_, v___y_2599_, v___y_2596_, v___y_2592_, v___y_2597_, v___y_2588_, v___y_2590_, v___y_2591_, v___y_2598_, v___y_2600_, v___y_2593_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_n(v_a_2602_, 2);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2602_, v___y_2595_, v___y_2599_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref_known(v___x_2603_, 1);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2602_, v___y_2595_, v___y_2599_);
v___y_2577_ = v___y_2595_;
v___y_2578_ = v___x_2604_;
goto v___jp_2576_;
}
else
{
lean_dec(v_a_2602_);
v___y_2577_ = v___y_2595_;
v___y_2578_ = v___x_2603_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v___y_2595_);
v_a_2605_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2601_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
v___jp_2613_:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2615_, v___y_2620_, v___y_2621_, v___y_2625_, v___y_2622_, v___y_2618_, v___y_2623_, v___y_2614_, v___y_2616_, v___y_2617_, v___y_2624_, v___y_2626_, v___y_2619_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2628_, v___y_2621_, v___y_2625_);
v___y_2577_ = v___y_2621_;
v___y_2578_ = v___x_2629_;
goto v___jp_2576_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v___y_2621_);
v_a_2630_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2627_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2627_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec(v_a_3566_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3579_, v_x_3580_, v_x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3583_, lean_object* v_x_3584_, size_t v_x_3585_, size_t v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3584_, v_x_3585_, v_x_3586_, v_x_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
size_t v_x_529305__boxed_3596_; size_t v_x_529306__boxed_3597_; lean_object* v_res_3598_; 
v_x_529305__boxed_3596_ = lean_unbox_usize(v_x_3592_);
lean_dec(v_x_3592_);
v_x_529306__boxed_3597_ = lean_unbox_usize(v_x_3593_);
lean_dec(v_x_3593_);
v_res_3598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3590_, v_x_3591_, v_x_529305__boxed_3596_, v_x_529306__boxed_3597_, v_x_3594_, v_x_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3599_, lean_object* v_n_3600_, lean_object* v_k_3601_, lean_object* v_v_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3600_, v_k_3601_, v_v_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3604_, size_t v_depth_3605_, lean_object* v_keys_3606_, lean_object* v_vals_3607_, lean_object* v_heq_3608_, lean_object* v_i_3609_, lean_object* v_entries_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3605_, v_keys_3606_, v_vals_3607_, v_i_3609_, v_entries_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3612_, lean_object* v_depth_3613_, lean_object* v_keys_3614_, lean_object* v_vals_3615_, lean_object* v_heq_3616_, lean_object* v_i_3617_, lean_object* v_entries_3618_){
_start:
{
size_t v_depth_boxed_3619_; lean_object* v_res_3620_; 
v_depth_boxed_3619_ = lean_unbox_usize(v_depth_3613_);
lean_dec(v_depth_3613_);
v_res_3620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3612_, v_depth_boxed_3619_, v_keys_3614_, v_vals_3615_, v_heq_3616_, v_i_3617_, v_entries_3618_);
lean_dec_ref(v_vals_3615_);
lean_dec_ref(v_keys_3614_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3627_, lean_object* v_base_3628_, lean_object* v_natModuleInst_3629_, lean_object* v_declName_3630_, lean_object* v_le_3631_, lean_object* v_mid_3632_, lean_object* v_ord_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3635_, 0, v_val_3627_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_mkConst(v_declName_3630_, v___x_3635_);
v___x_3637_ = l_Lean_mkApp5(v___x_3636_, v_base_3628_, v_natModuleInst_3629_, v_le_3631_, v_mid_3632_, v_ord_3633_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3737_, lean_object* v_base_3738_, lean_object* v_natModuleInst_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v___x_3751_; 
lean_inc_ref(v_base_3738_);
v___x_3751_ = l_Lean_Meta_getDecLevel_x3f(v_base_3738_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_4489_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_4489_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_4489_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
if (lean_obj_tag(v_a_3752_) == 1)
{
lean_object* v_val_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_4484_; 
lean_del_object(v___x_3754_);
v_val_3756_ = lean_ctor_get(v_a_3752_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_a_3752_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_3758_ = v_a_3752_;
v_isShared_3759_ = v_isSharedCheck_4484_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_val_3756_);
lean_dec(v_a_3752_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_4484_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_a_3780_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_a_3852_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___x_4070_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v_noNatDivInstQ_x3f_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v_isLinearInstQ_x3f_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___x_4325_; 
v___x_4070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4070_, v_val_3756_, v_base_3738_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v_fst_4334_; lean_object* v_snd_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___x_4378_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_n(v_a_4326_, 2);
lean_dec_ref_known(v___x_4325_, 1);
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4378_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_3756_, v_base_3738_, v_a_4326_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v_orderedAddInst_x3f_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
if (lean_obj_tag(v_a_4326_) == 1)
{
if (lean_obj_tag(v_a_4379_) == 1)
{
lean_object* v_val_4440_; lean_object* v_val_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_val_4440_ = lean_ctor_get(v_a_4326_, 0);
v_val_4441_ = lean_ctor_get(v_a_4379_, 0);
v___x_4442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4442_, v_val_3756_, v_base_3738_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref_known(v___x_4443_, 1);
v___x_4445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4446_ = lean_box(0);
lean_inc(v_val_3756_);
v___x_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_val_3756_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
v___x_4448_ = l_Lean_mkConst(v___x_4445_, v___x_4447_);
lean_inc(v_val_4441_);
lean_inc(v_val_4440_);
lean_inc_ref(v_base_3738_);
v___x_4449_ = l_Lean_mkApp4(v___x_4448_, v_base_3738_, v_a_4444_, v_val_4440_, v_val_4441_);
v___x_4450_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4449_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref_known(v___x_4450_, 1);
v_orderedAddInst_x3f_4381_ = v_a_4451_;
v___y_4382_ = v_a_3740_;
v___y_4383_ = v_a_3741_;
v___y_4384_ = v_a_3742_;
v___y_4385_ = v_a_3743_;
v___y_4386_ = v_a_3744_;
v___y_4387_ = v_a_3745_;
v___y_4388_ = v_a_3746_;
v___y_4389_ = v_a_3747_;
v___y_4390_ = v_a_3748_;
v___y_4391_ = v_a_3749_;
goto v___jp_4380_;
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref_known(v_a_4379_, 1);
lean_dec_ref_known(v_a_4326_, 1);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4452_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4450_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4450_);
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
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref_known(v_a_4379_, 1);
lean_dec_ref_known(v_a_4326_, 1);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4460_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4443_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4443_);
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
v___y_4429_ = v_a_3740_;
v___y_4430_ = v_a_3741_;
v___y_4431_ = v_a_3742_;
v___y_4432_ = v_a_3743_;
v___y_4433_ = v_a_3744_;
v___y_4434_ = v_a_3745_;
v___y_4435_ = v_a_3746_;
v___y_4436_ = v_a_3747_;
v___y_4437_ = v_a_3748_;
v___y_4438_ = v_a_3749_;
goto v___jp_4428_;
}
}
else
{
v___y_4429_ = v_a_3740_;
v___y_4430_ = v_a_3741_;
v___y_4431_ = v_a_3742_;
v___y_4432_ = v_a_3743_;
v___y_4433_ = v_a_3744_;
v___y_4434_ = v_a_3745_;
v___y_4435_ = v_a_3746_;
v___y_4436_ = v_a_3747_;
v___y_4437_ = v_a_3748_;
v___y_4438_ = v_a_3749_;
goto v___jp_4428_;
}
v___jp_4380_:
{
if (lean_obj_tag(v_a_4326_) == 0)
{
lean_object* v___x_4392_; 
lean_dec(v_orderedAddInst_x3f_4381_);
lean_dec(v_a_4379_);
v___x_4392_ = lean_box(0);
v___y_4366_ = v___y_4385_;
v___y_4367_ = v___y_4388_;
v___y_4368_ = v___y_4382_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4389_;
v___y_4371_ = v___y_4391_;
v___y_4372_ = v___y_4390_;
v___y_4373_ = v___y_4383_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4386_;
v___y_4376_ = v___x_4392_;
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_a_4379_) == 0)
{
lean_object* v___x_4393_; 
lean_dec_ref_known(v_a_4326_, 1);
lean_dec(v_orderedAddInst_x3f_4381_);
v___x_4393_ = lean_box(0);
v___y_4366_ = v___y_4385_;
v___y_4367_ = v___y_4388_;
v___y_4368_ = v___y_4382_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4389_;
v___y_4371_ = v___y_4391_;
v___y_4372_ = v___y_4390_;
v___y_4373_ = v___y_4383_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4386_;
v___y_4376_ = v___x_4393_;
goto v___jp_4365_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4381_) == 0)
{
lean_object* v___x_4394_; 
lean_dec_ref_known(v_a_4379_, 1);
lean_dec_ref_known(v_a_4326_, 1);
v___x_4394_ = lean_box(0);
v___y_4366_ = v___y_4385_;
v___y_4367_ = v___y_4388_;
v___y_4368_ = v___y_4382_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4389_;
v___y_4371_ = v___y_4391_;
v___y_4372_ = v___y_4390_;
v___y_4373_ = v___y_4383_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4386_;
v___y_4376_ = v___x_4394_;
goto v___jp_4365_;
}
else
{
lean_object* v_val_4395_; lean_object* v_val_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4427_; 
v_val_4395_ = lean_ctor_get(v_a_4326_, 0);
v_val_4396_ = lean_ctor_get(v_a_4379_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_a_4379_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4398_ = v_a_4379_;
v_isShared_4399_ = v_isSharedCheck_4427_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_val_4396_);
lean_dec(v_a_4379_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4427_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_val_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4426_; 
v_val_4400_ = lean_ctor_get(v_orderedAddInst_x3f_4381_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_orderedAddInst_x3f_4381_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4402_ = v_orderedAddInst_x3f_4381_;
v_isShared_4403_ = v_isSharedCheck_4426_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_val_4400_);
lean_dec(v_orderedAddInst_x3f_4381_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4426_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4400_);
lean_inc(v_val_4396_);
lean_inc(v_val_4395_);
lean_inc_ref(v_natModuleInst_3739_);
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3756_, v_base_3738_, v_natModuleInst_3739_, v___x_4404_, v_val_4395_, v_val_4396_, v_val_4400_);
lean_inc_ref(v___x_4405_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4405_);
v___x_4407_ = v___x_4402_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4411_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4400_);
lean_inc(v_val_4396_);
lean_inc(v_val_4395_);
lean_inc_ref(v_natModuleInst_3739_);
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3756_, v_base_3738_, v_natModuleInst_3739_, v___x_4408_, v_val_4395_, v_val_4396_, v_val_4400_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4409_);
v___x_4411_ = v___x_4398_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4409_);
v___x_4411_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4400_, 2);
lean_inc(v_val_4396_);
lean_inc_n(v_val_4395_, 3);
lean_inc_ref_n(v_natModuleInst_3739_, 2);
lean_inc_ref_n(v_base_3738_, 2);
lean_inc_n(v_val_3756_, 3);
v___x_4413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3756_, v_base_3738_, v_natModuleInst_3739_, v___x_4412_, v_val_4395_, v_val_4396_, v_val_4400_);
v___x_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3756_, v_base_3738_, v_natModuleInst_3739_, v___x_4415_, v_val_4395_, v_val_4396_, v_val_4400_);
v___x_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4419_ = lean_box(0);
v___x_4420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_val_3756_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = l_Lean_mkConst(v___x_4418_, v___x_4420_);
lean_inc_ref(v_type_3737_);
v___x_4422_ = l_Lean_mkAppB(v___x_4421_, v_type_3737_, v___x_4405_);
v___x_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
v___y_4328_ = v___x_4417_;
v___y_4329_ = v___y_4391_;
v___y_4330_ = v___y_4390_;
v___y_4331_ = v___y_4383_;
v___y_4332_ = v___y_4384_;
v___y_4333_ = v___y_4386_;
v_fst_4334_ = v_val_4395_;
v_snd_4335_ = v_val_4400_;
v___y_4336_ = v___x_4414_;
v___y_4337_ = v___x_4411_;
v___y_4338_ = v___y_4385_;
v___y_4339_ = v___y_4388_;
v___y_4340_ = v___x_4407_;
v___y_4341_ = v___y_4382_;
v___y_4342_ = v___y_4387_;
v___y_4343_ = v___y_4389_;
v___y_4344_ = v___x_4423_;
goto v___jp_4327_;
}
}
}
}
}
}
}
}
v___jp_4428_:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_box(0);
v_orderedAddInst_x3f_4381_ = v___x_4439_;
v___y_4382_ = v___y_4429_;
v___y_4383_ = v___y_4430_;
v___y_4384_ = v___y_4431_;
v___y_4385_ = v___y_4432_;
v___y_4386_ = v___y_4433_;
v___y_4387_ = v___y_4434_;
v___y_4388_ = v___y_4435_;
v___y_4389_ = v___y_4436_;
v___y_4390_ = v___y_4437_;
v___y_4391_ = v___y_4438_;
goto v___jp_4380_;
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_a_4326_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4468_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4378_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4378_);
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
v___jp_4327_:
{
lean_object* v___x_4345_; 
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4345_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_3756_, v_base_3738_, v_a_4326_, v___y_4333_, v___y_4342_, v___y_4339_, v___y_4343_, v___y_4330_, v___y_4329_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref_known(v___x_4345_, 1);
if (lean_obj_tag(v_a_4346_) == 0)
{
lean_dec_ref(v_snd_4335_);
lean_dec_ref(v_fst_4334_);
v___y_4252_ = v___y_4328_;
v___y_4253_ = v___y_4336_;
v___y_4254_ = v___y_4337_;
v___y_4255_ = v___y_4340_;
v___y_4256_ = v___y_4344_;
v_isLinearInstQ_x3f_4257_ = v_a_4346_;
v___y_4258_ = v___y_4341_;
v___y_4259_ = v___y_4331_;
v___y_4260_ = v___y_4332_;
v___y_4261_ = v___y_4338_;
v___y_4262_ = v___y_4333_;
v___y_4263_ = v___y_4342_;
v___y_4264_ = v___y_4339_;
v___y_4265_ = v___y_4343_;
v___y_4266_ = v___y_4330_;
v___y_4267_ = v___y_4329_;
goto v___jp_4251_;
}
else
{
lean_object* v_val_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4356_; 
v_val_4347_ = lean_ctor_get(v_a_4346_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_a_4346_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4349_ = v_a_4346_;
v_isShared_4350_ = v_isSharedCheck_4356_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_val_4347_);
lean_dec(v_a_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4356_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3739_);
lean_inc_ref(v_base_3738_);
lean_inc(v_val_3756_);
v___x_4352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3756_, v_base_3738_, v_natModuleInst_3739_, v___x_4351_, v_fst_4334_, v_val_4347_, v_snd_4335_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4352_);
v___x_4354_ = v___x_4349_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
v___y_4252_ = v___y_4328_;
v___y_4253_ = v___y_4336_;
v___y_4254_ = v___y_4337_;
v___y_4255_ = v___y_4340_;
v___y_4256_ = v___y_4344_;
v_isLinearInstQ_x3f_4257_ = v___x_4354_;
v___y_4258_ = v___y_4341_;
v___y_4259_ = v___y_4331_;
v___y_4260_ = v___y_4332_;
v___y_4261_ = v___y_4338_;
v___y_4262_ = v___y_4333_;
v___y_4263_ = v___y_4342_;
v___y_4264_ = v___y_4339_;
v___y_4265_ = v___y_4343_;
v___y_4266_ = v___y_4330_;
v___y_4267_ = v___y_4329_;
goto v___jp_4251_;
}
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v___y_4344_);
lean_dec(v___y_4340_);
lean_dec(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v_snd_4335_);
lean_dec_ref(v_fst_4334_);
lean_dec(v___y_4328_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4357_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4345_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4345_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
v___jp_4365_:
{
lean_object* v___x_4377_; 
v___x_4377_ = lean_box(0);
v___y_4252_ = v___x_4377_;
v___y_4253_ = v___x_4377_;
v___y_4254_ = v___x_4377_;
v___y_4255_ = v___x_4377_;
v___y_4256_ = v___x_4377_;
v_isLinearInstQ_x3f_4257_ = v___x_4377_;
v___y_4258_ = v___y_4368_;
v___y_4259_ = v___y_4373_;
v___y_4260_ = v___y_4374_;
v___y_4261_ = v___y_4366_;
v___y_4262_ = v___y_4375_;
v___y_4263_ = v___y_4369_;
v___y_4264_ = v___y_4367_;
v___y_4265_ = v___y_4370_;
v___y_4266_ = v___y_4372_;
v___y_4267_ = v___y_4371_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4476_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4325_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4325_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
v___jp_3760_:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3768_, v___y_3765_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v_structs_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v_structs_3783_ = lean_ctor_get(v_a_3782_, 0);
lean_inc_ref(v_structs_3783_);
lean_dec(v_a_3782_);
v___x_3784_ = lean_array_get_size(v_structs_3783_);
lean_dec_ref(v_structs_3783_);
v___x_3785_ = lean_box(0);
lean_inc_ref(v___y_3761_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___y_3761_);
v___x_3787_ = v___x_3758_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___y_3761_);
v___x_3787_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___f_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_inc_ref(v___y_3774_);
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___y_3774_);
v___x_3789_ = lean_unsigned_to_nat(32u);
v___x_3790_ = lean_mk_empty_array_with_capacity(v___x_3789_);
v___x_3791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3792_ = ((size_t)5ULL);
lean_inc(v___y_3777_);
v___x_3793_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3790_);
lean_ctor_set(v___x_3793_, 2, v___y_3777_);
lean_ctor_set(v___x_3793_, 3, v___y_3777_);
lean_ctor_set_usize(v___x_3793_, 4, v___x_3792_);
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3795_ = 0;
v___x_3796_ = lean_box(0);
lean_inc_ref_n(v___x_3793_, 7);
v___x_3797_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3797_, 0, v___x_3784_);
lean_ctor_set(v___x_3797_, 1, v___x_3785_);
lean_ctor_set(v___x_3797_, 2, v_type_3737_);
lean_ctor_set(v___x_3797_, 3, v_val_3756_);
lean_ctor_set(v___x_3797_, 4, v___y_3773_);
lean_ctor_set(v___x_3797_, 5, v___y_3778_);
lean_ctor_set(v___x_3797_, 6, v___y_3776_);
lean_ctor_set(v___x_3797_, 7, v___y_3772_);
lean_ctor_set(v___x_3797_, 8, v___y_3775_);
lean_ctor_set(v___x_3797_, 9, v___y_3766_);
lean_ctor_set(v___x_3797_, 10, v___y_3762_);
lean_ctor_set(v___x_3797_, 11, v___y_3763_);
lean_ctor_set(v___x_3797_, 12, v___x_3785_);
lean_ctor_set(v___x_3797_, 13, v___x_3785_);
lean_ctor_set(v___x_3797_, 14, v___x_3785_);
lean_ctor_set(v___x_3797_, 15, v___x_3785_);
lean_ctor_set(v___x_3797_, 16, v___x_3785_);
lean_ctor_set(v___x_3797_, 17, v___y_3769_);
lean_ctor_set(v___x_3797_, 18, v___y_3767_);
lean_ctor_set(v___x_3797_, 19, v___x_3785_);
lean_ctor_set(v___x_3797_, 20, v___y_3764_);
lean_ctor_set(v___x_3797_, 21, v_a_3780_);
lean_ctor_set(v___x_3797_, 22, v___y_3771_);
lean_ctor_set(v___x_3797_, 23, v___y_3761_);
lean_ctor_set(v___x_3797_, 24, v___y_3774_);
lean_ctor_set(v___x_3797_, 25, v___x_3787_);
lean_ctor_set(v___x_3797_, 26, v___x_3788_);
lean_ctor_set(v___x_3797_, 27, v___x_3785_);
lean_ctor_set(v___x_3797_, 28, v___y_3770_);
lean_ctor_set(v___x_3797_, 29, v___y_3779_);
lean_ctor_set(v___x_3797_, 30, v___x_3793_);
lean_ctor_set(v___x_3797_, 31, v___x_3794_);
lean_ctor_set(v___x_3797_, 32, v___x_3793_);
lean_ctor_set(v___x_3797_, 33, v___x_3793_);
lean_ctor_set(v___x_3797_, 34, v___x_3793_);
lean_ctor_set(v___x_3797_, 35, v___x_3793_);
lean_ctor_set(v___x_3797_, 36, v___x_3785_);
lean_ctor_set(v___x_3797_, 37, v___x_3794_);
lean_ctor_set(v___x_3797_, 38, v___x_3793_);
lean_ctor_set(v___x_3797_, 39, v___x_3796_);
lean_ctor_set(v___x_3797_, 40, v___x_3793_);
lean_ctor_set(v___x_3797_, 41, v___x_3793_);
lean_ctor_set_uint8(v___x_3797_, sizeof(void*)*42, v___x_3795_);
v___f_3798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_3798_, 0, v___x_3797_);
v___x_3799_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3800_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3799_, v___f_3798_, v___y_3768_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v___x_3800_, 0);
lean_dec(v_unused_3809_);
v___x_3802_ = v___x_3800_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v___x_3800_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3784_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3804_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_a_3810_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3800_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3800_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v_a_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3819_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3781_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3781_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
v___jp_3827_:
{
if (lean_obj_tag(v___y_3846_) == 0)
{
lean_dec(v___y_3833_);
v___y_3761_ = v___y_3828_;
v___y_3762_ = v___y_3829_;
v___y_3763_ = v___y_3830_;
v___y_3764_ = v_a_3852_;
v___y_3765_ = v___y_3831_;
v___y_3766_ = v___y_3832_;
v___y_3767_ = v___y_3834_;
v___y_3768_ = v___y_3835_;
v___y_3769_ = v___y_3836_;
v___y_3770_ = v___y_3838_;
v___y_3771_ = v___y_3841_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3843_;
v___y_3774_ = v___y_3845_;
v___y_3775_ = v___y_3844_;
v___y_3776_ = v___y_3846_;
v___y_3777_ = v___y_3848_;
v___y_3778_ = v___y_3849_;
v___y_3779_ = v___y_3851_;
v_a_3780_ = v___y_3846_;
goto v___jp_3760_;
}
else
{
lean_object* v_val_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_val_3853_ = lean_ctor_get(v___y_3846_, 0);
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3855_ = l_Lean_mkConst(v___x_3854_, v___y_3833_);
lean_inc(v_val_3853_);
lean_inc_ref(v_type_3737_);
v___x_3856_ = l_Lean_mkAppB(v___x_3855_, v_type_3737_, v_val_3853_);
v___x_3857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3856_, v___y_3839_, v___y_3840_, v___y_3837_, v___y_3847_, v___y_3831_, v___y_3850_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_a_3858_);
v___y_3761_ = v___y_3828_;
v___y_3762_ = v___y_3829_;
v___y_3763_ = v___y_3830_;
v___y_3764_ = v_a_3852_;
v___y_3765_ = v___y_3831_;
v___y_3766_ = v___y_3832_;
v___y_3767_ = v___y_3834_;
v___y_3768_ = v___y_3835_;
v___y_3769_ = v___y_3836_;
v___y_3770_ = v___y_3838_;
v___y_3771_ = v___y_3841_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3843_;
v___y_3774_ = v___y_3845_;
v___y_3775_ = v___y_3844_;
v___y_3776_ = v___y_3846_;
v___y_3777_ = v___y_3848_;
v___y_3778_ = v___y_3849_;
v___y_3779_ = v___y_3851_;
v_a_3780_ = v___x_3859_;
goto v___jp_3760_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref_known(v___y_3846_, 1);
lean_dec(v_a_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3832_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3860_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3857_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3857_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
v___jp_3868_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3883_);
v___x_3908_ = l_Lean_Name_mkStr2(v___y_3883_, v___x_3907_);
lean_inc(v___y_3873_);
v___x_3909_ = l_Lean_mkConst(v___x_3908_, v___y_3873_);
lean_inc_ref(v_type_3737_);
v___x_3910_ = l_Lean_mkAppB(v___x_3909_, v_type_3737_, v___y_3879_);
v___x_3911_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3910_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3892_);
v___x_3914_ = l_Lean_Name_mkStr2(v___y_3892_, v___x_3913_);
lean_inc(v___y_3873_);
v___x_3915_ = l_Lean_mkConst(v___x_3914_, v___y_3873_);
lean_inc_ref(v_type_3737_);
v___x_3916_ = l_Lean_mkApp3(v___x_3915_, v_type_3737_, v___y_3889_, v___y_3885_);
v___x_3917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3916_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3869_);
v___x_3920_ = l_Lean_Name_mkStr2(v___y_3869_, v___x_3919_);
lean_inc(v___y_3881_);
v___x_3921_ = l_Lean_mkConst(v___x_3920_, v___y_3881_);
lean_inc_ref_n(v_type_3737_, 3);
v___x_3922_ = l_Lean_mkApp4(v___x_3921_, v_type_3737_, v_type_3737_, v_type_3737_, v___y_3887_);
v___x_3923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3922_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3884_);
v___x_3926_ = l_Lean_Name_mkStr2(v___y_3884_, v___x_3925_);
v___x_3927_ = l_Lean_mkConst(v___x_3926_, v___y_3881_);
lean_inc_ref_n(v_type_3737_, 3);
v___x_3928_ = l_Lean_mkApp4(v___x_3927_, v_type_3737_, v_type_3737_, v_type_3737_, v___y_3895_);
v___x_3929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3928_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3877_);
v___x_3932_ = l_Lean_Name_mkStr2(v___y_3877_, v___x_3931_);
lean_inc(v___y_3873_);
v___x_3933_ = l_Lean_mkConst(v___x_3932_, v___y_3873_);
lean_inc_ref(v_type_3737_);
v___x_3934_ = l_Lean_mkAppB(v___x_3933_, v_type_3737_, v___y_3874_);
v___x_3935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3934_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3888_);
v___x_3938_ = l_Lean_Name_mkStr2(v___y_3888_, v___x_3937_);
v___x_3939_ = l_Lean_mkConst(v___x_3938_, v___y_3896_);
lean_inc_ref_n(v_type_3737_, 2);
lean_inc_ref(v___x_3939_);
v___x_3940_ = l_Lean_mkApp4(v___x_3939_, v___y_3890_, v_type_3737_, v_type_3737_, v___y_3894_);
v___x_3941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3940_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
lean_inc_ref_n(v_type_3737_, 2);
v___x_3943_ = l_Lean_mkApp4(v___x_3939_, v___y_3875_, v_type_3737_, v_type_3737_, v___y_3870_);
v___x_3944_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3943_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3944_) == 0)
{
if (lean_obj_tag(v___y_3882_) == 0)
{
lean_object* v_a_3945_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
v___y_3828_ = v_a_3942_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3886_;
v___y_3831_ = v___y_3905_;
v___y_3832_ = v___y_3872_;
v___y_3833_ = v___y_3873_;
v___y_3834_ = v_a_3918_;
v___y_3835_ = v___y_3897_;
v___y_3836_ = v_a_3912_;
v___y_3837_ = v___y_3903_;
v___y_3838_ = v_a_3930_;
v___y_3839_ = v___y_3901_;
v___y_3840_ = v___y_3902_;
v___y_3841_ = v_a_3924_;
v___y_3842_ = v___y_3891_;
v___y_3843_ = v___y_3876_;
v___y_3844_ = v___y_3893_;
v___y_3845_ = v_a_3945_;
v___y_3846_ = v___y_3878_;
v___y_3847_ = v___y_3904_;
v___y_3848_ = v___y_3880_;
v___y_3849_ = v___y_3882_;
v___y_3850_ = v___y_3906_;
v___y_3851_ = v_a_3936_;
v_a_3852_ = v___y_3882_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3946_; lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_a_3946_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3944_, 1);
v_val_3947_ = lean_ctor_get(v___y_3882_, 0);
v___x_3948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3873_);
v___x_3949_ = l_Lean_mkConst(v___x_3948_, v___y_3873_);
lean_inc(v_val_3947_);
lean_inc_ref(v_type_3737_);
v___x_3950_ = l_Lean_mkAppB(v___x_3949_, v_type_3737_, v_val_3947_);
v___x_3951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3950_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_a_3952_);
v___y_3828_ = v_a_3942_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3886_;
v___y_3831_ = v___y_3905_;
v___y_3832_ = v___y_3872_;
v___y_3833_ = v___y_3873_;
v___y_3834_ = v_a_3918_;
v___y_3835_ = v___y_3897_;
v___y_3836_ = v_a_3912_;
v___y_3837_ = v___y_3903_;
v___y_3838_ = v_a_3930_;
v___y_3839_ = v___y_3901_;
v___y_3840_ = v___y_3902_;
v___y_3841_ = v_a_3924_;
v___y_3842_ = v___y_3891_;
v___y_3843_ = v___y_3876_;
v___y_3844_ = v___y_3893_;
v___y_3845_ = v_a_3946_;
v___y_3846_ = v___y_3878_;
v___y_3847_ = v___y_3904_;
v___y_3848_ = v___y_3880_;
v___y_3849_ = v___y_3882_;
v___y_3850_ = v___y_3906_;
v___y_3851_ = v_a_3936_;
v_a_3852_ = v___x_3953_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_a_3946_);
lean_dec_ref_known(v___y_3882_, 1);
lean_dec(v_a_3942_);
lean_dec(v_a_3936_);
lean_dec(v_a_3930_);
lean_dec(v_a_3924_);
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3886_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3954_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3951_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3951_);
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
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_a_3942_);
lean_dec(v_a_3936_);
lean_dec(v_a_3930_);
lean_dec(v_a_3924_);
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3962_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3944_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3944_);
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
lean_dec_ref(v___x_3939_);
lean_dec(v_a_3936_);
lean_dec(v_a_3930_);
lean_dec(v_a_3924_);
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3970_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3941_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3941_);
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
lean_dec(v_a_3930_);
lean_dec(v_a_3924_);
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3978_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3935_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3935_);
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
lean_dec(v_a_3924_);
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3986_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3929_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3929_);
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
lean_dec(v_a_3918_);
lean_dec(v_a_3912_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_3994_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3923_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3923_);
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
lean_dec(v_a_3912_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4002_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3917_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3917_);
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
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4010_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3911_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3911_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
v___jp_4018_:
{
if (lean_obj_tag(v___y_4029_) == 1)
{
lean_object* v_val_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_val_4057_ = lean_ctor_get(v___y_4029_, 0);
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_4023_);
v___x_4059_ = l_Lean_mkConst(v___x_4058_, v___y_4023_);
lean_inc_ref(v_type_3737_);
v___x_4060_ = l_Lean_Expr_app___override(v___x_4059_, v_type_3737_);
lean_inc(v_val_4057_);
v___x_4061_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4060_, v_val_4057_, v___y_4052_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_dec_ref_known(v___x_4061_, 1);
v___y_3869_ = v___y_4021_;
v___y_3870_ = v___y_4020_;
v___y_3871_ = v___y_4019_;
v___y_3872_ = v___y_4022_;
v___y_3873_ = v___y_4023_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4026_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4029_;
v___y_3879_ = v___y_4028_;
v___y_3880_ = v___y_4031_;
v___y_3881_ = v___y_4030_;
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
v___y_3899_ = v___y_4049_;
v___y_3900_ = v___y_4050_;
v___y_3901_ = v___y_4051_;
v___y_3902_ = v___y_4052_;
v___y_3903_ = v___y_4053_;
v___y_3904_ = v___y_4054_;
v___y_3905_ = v___y_4055_;
v___y_3906_ = v___y_4056_;
goto v___jp_3868_;
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec_ref_known(v___y_4029_, 1);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4028_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
v___y_3869_ = v___y_4021_;
v___y_3870_ = v___y_4020_;
v___y_3871_ = v___y_4019_;
v___y_3872_ = v___y_4022_;
v___y_3873_ = v___y_4023_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4026_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4029_;
v___y_3879_ = v___y_4028_;
v___y_3880_ = v___y_4031_;
v___y_3881_ = v___y_4030_;
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
v___y_3899_ = v___y_4049_;
v___y_3900_ = v___y_4050_;
v___y_3901_ = v___y_4051_;
v___y_3902_ = v___y_4052_;
v___y_3903_ = v___y_4053_;
v___y_3904_ = v___y_4054_;
v___y_3905_ = v___y_4055_;
v___y_3906_ = v___y_4056_;
goto v___jp_3868_;
}
}
v___jp_4071_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4076_, 14);
v___x_4091_ = l_Lean_mkConst(v___x_4090_, v___y_4076_);
v___x_4092_ = l_Lean_mkAppB(v___x_4091_, v_base_3738_, v_natModuleInst_3739_);
v___x_4093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4094_ = l_Lean_mkConst(v___x_4093_, v___y_4076_);
lean_inc_ref_n(v___x_4092_, 4);
lean_inc_ref_n(v_type_3737_, 14);
v___x_4095_ = l_Lean_mkAppB(v___x_4094_, v_type_3737_, v___x_4092_);
v___x_4096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4097_ = l_Lean_mkConst(v___x_4096_, v___y_4076_);
lean_inc_ref_n(v___x_4095_, 2);
v___x_4098_ = l_Lean_mkAppB(v___x_4097_, v_type_3737_, v___x_4095_);
v___x_4099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4100_ = l_Lean_mkConst(v___x_4099_, v___y_4076_);
lean_inc_ref(v___x_4098_);
v___x_4101_ = l_Lean_mkAppB(v___x_4100_, v_type_3737_, v___x_4098_);
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4104_ = l_Lean_mkConst(v___x_4103_, v___y_4076_);
lean_inc_ref(v___x_4101_);
v___x_4105_ = l_Lean_mkAppB(v___x_4104_, v_type_3737_, v___x_4101_);
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4107_ = l_Lean_mkConst(v___x_4106_, v___y_4076_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4109_ = l_Lean_mkConst(v___x_4108_, v___y_4076_);
v___x_4110_ = l_Lean_mkAppB(v___x_4109_, v_type_3737_, v___x_4098_);
v___x_4111_ = l_Lean_mkAppB(v___x_4107_, v_type_3737_, v___x_4110_);
v___x_4112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4113_ = l_Lean_mkConst(v___x_4112_, v___y_4076_);
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4115_ = l_Lean_mkConst(v___x_4114_, v___y_4076_);
v___x_4116_ = l_Lean_mkAppB(v___x_4115_, v_type_3737_, v___x_4095_);
v___x_4117_ = l_Lean_mkAppB(v___x_4113_, v_type_3737_, v___x_4116_);
v___x_4118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4119_ = l_Lean_mkConst(v___x_4118_, v___y_4076_);
v___x_4120_ = l_Lean_mkAppB(v___x_4119_, v_type_3737_, v___x_4095_);
v___x_4121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v___y_4076_);
v___x_4125_ = l_Lean_mkConst(v___x_4121_, v___x_4124_);
v___x_4126_ = l_Lean_Int_mkType;
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4128_ = l_Lean_mkConst(v___x_4127_, v___y_4076_);
v___x_4129_ = l_Lean_mkAppB(v___x_4128_, v_type_3737_, v___x_4092_);
lean_inc_ref(v___x_4125_);
v___x_4130_ = l_Lean_mkApp3(v___x_4125_, v___x_4126_, v_type_3737_, v___x_4129_);
v___x_4131_ = l_Lean_Nat_mkType;
v___x_4132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4133_ = l_Lean_mkConst(v___x_4132_, v___y_4076_);
v___x_4134_ = l_Lean_mkAppB(v___x_4133_, v_type_3737_, v___x_4092_);
v___x_4135_ = l_Lean_mkApp3(v___x_4125_, v___x_4131_, v_type_3737_, v___x_4134_);
v___x_4136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4137_ = l_Lean_mkConst(v___x_4136_, v___y_4076_);
v___x_4138_ = l_Lean_Expr_app___override(v___x_4137_, v_type_3737_);
v___x_4139_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4138_, v___x_4092_, v___y_4085_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec_ref_known(v___x_4139_, 1);
v___x_4140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4076_);
v___x_4141_ = l_Lean_mkConst(v___x_4140_, v___y_4076_);
lean_inc_ref(v_type_3737_);
v___x_4142_ = l_Lean_Expr_app___override(v___x_4141_, v_type_3737_);
lean_inc_ref(v___x_4101_);
v___x_4143_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4142_, v___x_4101_, v___y_4085_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec_ref_known(v___x_4143_, 1);
v___x_4144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4076_);
v___x_4146_ = l_Lean_mkConst(v___x_4145_, v___y_4076_);
v___x_4147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3737_);
v___x_4148_ = l_Lean_mkAppB(v___x_4146_, v_type_3737_, v___x_4147_);
lean_inc_ref(v___x_4105_);
v___x_4149_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4148_, v___x_4105_, v___y_4085_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec_ref_known(v___x_4149_, 1);
v___x_4150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4076_);
lean_inc_n(v_val_3756_, 2);
v___x_4152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_val_3756_);
lean_ctor_set(v___x_4152_, 1, v___y_4076_);
lean_inc_ref(v___x_4152_);
v___x_4153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4153_, 0, v_val_3756_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
lean_inc_ref(v___x_4153_);
v___x_4154_ = l_Lean_mkConst(v___x_4151_, v___x_4153_);
lean_inc_ref_n(v_type_3737_, 3);
v___x_4155_ = l_Lean_mkApp3(v___x_4154_, v_type_3737_, v_type_3737_, v_type_3737_);
lean_inc_ref(v___x_4111_);
v___x_4156_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4155_, v___x_4111_, v___y_4085_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec_ref_known(v___x_4156_, 1);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4153_);
v___x_4159_ = l_Lean_mkConst(v___x_4158_, v___x_4153_);
lean_inc_ref_n(v_type_3737_, 3);
v___x_4160_ = l_Lean_mkApp3(v___x_4159_, v_type_3737_, v_type_3737_, v_type_3737_);
lean_inc_ref(v___x_4117_);
v___x_4161_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4160_, v___x_4117_, v___y_4085_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec_ref_known(v___x_4161_, 1);
v___x_4162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4076_);
v___x_4164_ = l_Lean_mkConst(v___x_4163_, v___y_4076_);
lean_inc_ref(v_type_3737_);
v___x_4165_ = l_Lean_Expr_app___override(v___x_4164_, v_type_3737_);
lean_inc_ref(v___x_4120_);
v___x_4166_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4165_, v___x_4120_, v___y_4085_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec_ref_known(v___x_4166_, 1);
v___x_4167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4123_);
lean_ctor_set(v___x_4169_, 1, v___x_4152_);
lean_inc_ref(v___x_4169_);
v___x_4170_ = l_Lean_mkConst(v___x_4168_, v___x_4169_);
lean_inc_ref_n(v_type_3737_, 2);
lean_inc_ref(v___x_4170_);
v___x_4171_ = l_Lean_mkApp3(v___x_4170_, v___x_4126_, v_type_3737_, v_type_3737_);
lean_inc_ref(v___x_4130_);
v___x_4172_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4171_, v___x_4130_, v___y_4085_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec_ref_known(v___x_4172_, 1);
lean_inc_ref_n(v_type_3737_, 2);
v___x_4173_ = l_Lean_mkApp3(v___x_4170_, v___x_4131_, v_type_3737_, v_type_3737_);
lean_inc_ref(v___x_4135_);
v___x_4174_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4173_, v___x_4135_, v___y_4085_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_dec_ref_known(v___x_4174_, 1);
if (lean_obj_tag(v___y_4077_) == 1)
{
lean_object* v_val_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_val_4175_ = lean_ctor_get(v___y_4077_, 0);
lean_inc(v___y_4076_);
v___x_4176_ = l_Lean_mkConst(v___x_4070_, v___y_4076_);
lean_inc_ref(v_type_3737_);
v___x_4177_ = l_Lean_Expr_app___override(v___x_4176_, v_type_3737_);
lean_inc(v_val_4175_);
v___x_4178_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4177_, v_val_4175_, v___y_4085_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_dec_ref_known(v___x_4178_, 1);
v___y_4019_ = v___y_4072_;
v___y_4020_ = v___x_4135_;
v___y_4021_ = v___x_4150_;
v___y_4022_ = v___y_4074_;
v___y_4023_ = v___y_4076_;
v___y_4024_ = v___x_4120_;
v___y_4025_ = v___x_4131_;
v___y_4026_ = v___x_4092_;
v___y_4027_ = v___x_4162_;
v___y_4028_ = v___x_4101_;
v___y_4029_ = v___y_4075_;
v___y_4030_ = v___x_4153_;
v___y_4031_ = v___x_4122_;
v___y_4032_ = v___y_4077_;
v___y_4033_ = v___x_4102_;
v___y_4034_ = v___x_4157_;
v___y_4035_ = v___x_4105_;
v___y_4036_ = v_noNatDivInstQ_x3f_4079_;
v___y_4037_ = v___x_4111_;
v___y_4038_ = v___x_4167_;
v___y_4039_ = v___x_4147_;
v___y_4040_ = v___x_4126_;
v___y_4041_ = v___y_4078_;
v___y_4042_ = v___x_4144_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___x_4130_;
v___y_4045_ = v___x_4117_;
v___y_4046_ = v___x_4169_;
v___y_4047_ = v___y_4080_;
v___y_4048_ = v___y_4081_;
v___y_4049_ = v___y_4082_;
v___y_4050_ = v___y_4083_;
v___y_4051_ = v___y_4084_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4086_;
v___y_4054_ = v___y_4087_;
v___y_4055_ = v___y_4088_;
v___y_4056_ = v___y_4089_;
goto v___jp_4018_;
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec_ref_known(v___y_4077_, 1);
lean_dec_ref_known(v___x_4169_, 2);
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4178_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4178_);
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
v___y_4019_ = v___y_4072_;
v___y_4020_ = v___x_4135_;
v___y_4021_ = v___x_4150_;
v___y_4022_ = v___y_4074_;
v___y_4023_ = v___y_4076_;
v___y_4024_ = v___x_4120_;
v___y_4025_ = v___x_4131_;
v___y_4026_ = v___x_4092_;
v___y_4027_ = v___x_4162_;
v___y_4028_ = v___x_4101_;
v___y_4029_ = v___y_4075_;
v___y_4030_ = v___x_4153_;
v___y_4031_ = v___x_4122_;
v___y_4032_ = v___y_4077_;
v___y_4033_ = v___x_4102_;
v___y_4034_ = v___x_4157_;
v___y_4035_ = v___x_4105_;
v___y_4036_ = v_noNatDivInstQ_x3f_4079_;
v___y_4037_ = v___x_4111_;
v___y_4038_ = v___x_4167_;
v___y_4039_ = v___x_4147_;
v___y_4040_ = v___x_4126_;
v___y_4041_ = v___y_4078_;
v___y_4042_ = v___x_4144_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___x_4130_;
v___y_4045_ = v___x_4117_;
v___y_4046_ = v___x_4169_;
v___y_4047_ = v___y_4080_;
v___y_4048_ = v___y_4081_;
v___y_4049_ = v___y_4082_;
v___y_4050_ = v___y_4083_;
v___y_4051_ = v___y_4084_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4086_;
v___y_4054_ = v___y_4087_;
v___y_4055_ = v___y_4088_;
v___y_4056_ = v___y_4089_;
goto v___jp_4018_;
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref_known(v___x_4169_, 2);
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4187_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4174_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4174_);
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
lean_dec_ref(v___x_4170_);
lean_dec_ref_known(v___x_4169_, 2);
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4195_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4172_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4172_);
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
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref_known(v___x_4152_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4203_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4166_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4166_);
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
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref_known(v___x_4152_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4211_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4161_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4161_);
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
lean_dec_ref_known(v___x_4153_, 2);
lean_dec_ref_known(v___x_4152_, 2);
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4219_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4156_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4156_);
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
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4227_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4149_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4149_);
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
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4235_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4143_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4143_);
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
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___x_4135_);
lean_dec_ref(v___x_4130_);
lean_dec_ref(v___x_4120_);
lean_dec_ref(v___x_4117_);
lean_dec_ref(v___x_4111_);
lean_dec_ref(v___x_4105_);
lean_dec_ref(v___x_4101_);
lean_dec_ref(v___x_4092_);
lean_dec(v_noNatDivInstQ_x3f_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_type_3737_);
v_a_4243_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4139_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4139_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
v___jp_4251_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4269_ = lean_box(0);
lean_inc(v_val_3756_);
v___x_4270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4270_, 0, v_val_3756_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
lean_inc_ref(v___x_4270_);
v___x_4271_ = l_Lean_mkConst(v___x_4268_, v___x_4270_);
lean_inc_ref(v_base_3738_);
v___x_4272_ = l_Lean_Expr_app___override(v___x_4271_, v_base_3738_);
v___x_4273_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4272_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
if (lean_obj_tag(v_a_4274_) == 1)
{
lean_object* v_val_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_val_4275_ = lean_ctor_get(v_a_4274_, 0);
lean_inc(v_val_4275_);
lean_dec_ref_known(v_a_4274_, 1);
v___x_4276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4270_);
v___x_4277_ = l_Lean_mkConst(v___x_4276_, v___x_4270_);
lean_inc_ref(v_base_3738_);
v___x_4278_ = l_Lean_mkAppB(v___x_4277_, v_base_3738_, v_val_4275_);
v___x_4279_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4278_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
if (lean_obj_tag(v_a_4280_) == 1)
{
lean_object* v_val_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_val_4281_ = lean_ctor_get(v_a_4280_, 0);
lean_inc(v_val_4281_);
lean_dec_ref_known(v_a_4280_, 1);
v___x_4282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4270_);
v___x_4283_ = l_Lean_mkConst(v___x_4282_, v___x_4270_);
lean_inc_ref(v_natModuleInst_3739_);
lean_inc_ref(v_base_3738_);
v___x_4284_ = l_Lean_mkAppB(v___x_4283_, v_base_3738_, v_natModuleInst_3739_);
v___x_4285_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4284_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
if (lean_obj_tag(v_a_4286_) == 1)
{
lean_object* v_val_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4297_; 
v_val_4287_ = lean_ctor_get(v_a_4286_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v_a_4286_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4289_ = v_a_4286_;
v_isShared_4290_ = v_isSharedCheck_4297_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_val_4287_);
lean_dec(v_a_4286_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4297_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4270_);
v___x_4292_ = l_Lean_mkConst(v___x_4291_, v___x_4270_);
lean_inc_ref(v_natModuleInst_3739_);
lean_inc_ref(v_base_3738_);
v___x_4293_ = l_Lean_mkApp4(v___x_4292_, v_base_3738_, v_natModuleInst_3739_, v_val_4281_, v_val_4287_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 0, v___x_4293_);
v___x_4295_ = v___x_4289_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
v___y_4072_ = v_isLinearInstQ_x3f_4257_;
v___y_4073_ = v___y_4253_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___x_4270_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v_noNatDivInstQ_x3f_4079_ = v___x_4295_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
goto v___jp_4071_;
}
}
}
else
{
lean_object* v___x_4298_; 
lean_dec(v_a_4286_);
lean_dec(v_val_4281_);
v___x_4298_ = lean_box(0);
v___y_4072_ = v_isLinearInstQ_x3f_4257_;
v___y_4073_ = v___y_4253_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___x_4270_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v_noNatDivInstQ_x3f_4079_ = v___x_4298_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
goto v___jp_4071_;
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_val_4281_);
lean_dec_ref_known(v___x_4270_, 2);
lean_dec(v_isLinearInstQ_x3f_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec(v___y_4252_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4299_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4285_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4285_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_object* v___x_4307_; 
lean_dec(v_a_4280_);
v___x_4307_ = lean_box(0);
v___y_4072_ = v_isLinearInstQ_x3f_4257_;
v___y_4073_ = v___y_4253_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___x_4270_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v_noNatDivInstQ_x3f_4079_ = v___x_4307_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
goto v___jp_4071_;
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref_known(v___x_4270_, 2);
lean_dec(v_isLinearInstQ_x3f_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec(v___y_4252_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4308_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4279_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4279_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v___x_4316_; 
lean_dec(v_a_4274_);
v___x_4316_ = lean_box(0);
v___y_4072_ = v_isLinearInstQ_x3f_4257_;
v___y_4073_ = v___y_4253_;
v___y_4074_ = v___y_4252_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___x_4270_;
v___y_4077_ = v___y_4255_;
v___y_4078_ = v___y_4256_;
v_noNatDivInstQ_x3f_4079_ = v___x_4316_;
v___y_4080_ = v___y_4258_;
v___y_4081_ = v___y_4259_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
goto v___jp_4071_;
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec_ref_known(v___x_4270_, 2);
lean_dec(v_isLinearInstQ_x3f_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec(v___y_4252_);
lean_del_object(v___x_3758_);
lean_dec(v_val_3756_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4317_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4273_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4273_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
}
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4487_; 
lean_dec(v_a_3752_);
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v___x_4485_ = lean_box(0);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_4485_);
v___x_4487_ = v___x_3754_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
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
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v_natModuleInst_3739_);
lean_dec_ref(v_base_3738_);
lean_dec_ref(v_type_3737_);
v_a_4490_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_3751_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_3751_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4498_, lean_object* v_base_4499_, lean_object* v_natModuleInst_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4498_, v_base_4499_, v_natModuleInst_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec(v_a_4501_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4533_ = lean_unsigned_to_nat(2u);
v___x_4534_ = l_Lean_Expr_isAppOfArity(v_type_4520_, v___x_4532_, v___x_4533_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; 
v___x_4535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4535_;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4536_ = l_Lean_Expr_appFn_x21(v_type_4520_);
v___x_4537_ = l_Lean_Expr_appArg_x21(v___x_4536_);
lean_dec_ref(v___x_4536_);
v___x_4538_ = l_Lean_Expr_appArg_x21(v_type_4520_);
v___x_4539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4520_, v___x_4537_, v___x_4538_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
return v___x_4539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec(v_a_4541_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4553_, lean_object* v_a_4554_, lean_object* v_s_4555_){
_start:
{
lean_object* v_structs_4556_; lean_object* v_typeIdOf_4557_; lean_object* v_exprToStructId_4558_; lean_object* v_exprToStructIdEntries_4559_; lean_object* v_forbiddenNatModules_4560_; lean_object* v_natStructs_4561_; lean_object* v_natTypeIdOf_4562_; lean_object* v_exprToNatStructId_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4571_; 
v_structs_4556_ = lean_ctor_get(v_s_4555_, 0);
v_typeIdOf_4557_ = lean_ctor_get(v_s_4555_, 1);
v_exprToStructId_4558_ = lean_ctor_get(v_s_4555_, 2);
v_exprToStructIdEntries_4559_ = lean_ctor_get(v_s_4555_, 3);
v_forbiddenNatModules_4560_ = lean_ctor_get(v_s_4555_, 4);
v_natStructs_4561_ = lean_ctor_get(v_s_4555_, 5);
v_natTypeIdOf_4562_ = lean_ctor_get(v_s_4555_, 6);
v_exprToNatStructId_4563_ = lean_ctor_get(v_s_4555_, 7);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_s_4555_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4565_ = v_s_4555_;
v_isShared_4566_ = v_isSharedCheck_4571_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_exprToNatStructId_4563_);
lean_inc(v_natTypeIdOf_4562_);
lean_inc(v_natStructs_4561_);
lean_inc(v_forbiddenNatModules_4560_);
lean_inc(v_exprToStructIdEntries_4559_);
lean_inc(v_exprToStructId_4558_);
lean_inc(v_typeIdOf_4557_);
lean_inc(v_structs_4556_);
lean_dec(v_s_4555_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4571_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4567_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4557_, v_type_4553_, v_a_4554_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 1, v___x_4567_);
v___x_4569_ = v___x_4565_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_structs_4556_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_exprToStructId_4558_);
lean_ctor_set(v_reuseFailAlloc_4570_, 3, v_exprToStructIdEntries_4559_);
lean_ctor_set(v_reuseFailAlloc_4570_, 4, v_forbiddenNatModules_4560_);
lean_ctor_set(v_reuseFailAlloc_4570_, 5, v_natStructs_4561_);
lean_ctor_set(v_reuseFailAlloc_4570_, 6, v_natTypeIdOf_4562_);
lean_ctor_set(v_reuseFailAlloc_4570_, 7, v_exprToNatStructId_4563_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4572_, lean_object* v_vals_4573_, lean_object* v_i_4574_, lean_object* v_k_4575_){
_start:
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = lean_array_get_size(v_keys_4572_);
v___x_4577_ = lean_nat_dec_lt(v_i_4574_, v___x_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; 
lean_dec(v_i_4574_);
v___x_4578_ = lean_box(0);
return v___x_4578_;
}
else
{
lean_object* v_k_x27_4579_; size_t v___x_4580_; size_t v___x_4581_; uint8_t v___x_4582_; 
v_k_x27_4579_ = lean_array_fget_borrowed(v_keys_4572_, v_i_4574_);
v___x_4580_ = lean_ptr_addr(v_k_4575_);
v___x_4581_ = lean_ptr_addr(v_k_x27_4579_);
v___x_4582_ = lean_usize_dec_eq(v___x_4580_, v___x_4581_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4583_ = lean_unsigned_to_nat(1u);
v___x_4584_ = lean_nat_add(v_i_4574_, v___x_4583_);
lean_dec(v_i_4574_);
v_i_4574_ = v___x_4584_;
goto _start;
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = lean_array_fget_borrowed(v_vals_4573_, v_i_4574_);
lean_dec(v_i_4574_);
lean_inc(v___x_4586_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4588_, lean_object* v_vals_4589_, lean_object* v_i_4590_, lean_object* v_k_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4588_, v_vals_4589_, v_i_4590_, v_k_4591_);
lean_dec_ref(v_k_4591_);
lean_dec_ref(v_vals_4589_);
lean_dec_ref(v_keys_4588_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4593_, size_t v_x_4594_, lean_object* v_x_4595_){
_start:
{
if (lean_obj_tag(v_x_4593_) == 0)
{
lean_object* v_es_4596_; lean_object* v___x_4597_; size_t v___x_4598_; size_t v___x_4599_; lean_object* v_j_4600_; lean_object* v___x_4601_; 
v_es_4596_ = lean_ctor_get(v_x_4593_, 0);
v___x_4597_ = lean_box(2);
v___x_4598_ = ((size_t)31ULL);
v___x_4599_ = lean_usize_land(v_x_4594_, v___x_4598_);
v_j_4600_ = lean_usize_to_nat(v___x_4599_);
v___x_4601_ = lean_array_get_borrowed(v___x_4597_, v_es_4596_, v_j_4600_);
lean_dec(v_j_4600_);
switch(lean_obj_tag(v___x_4601_))
{
case 0:
{
lean_object* v_key_4602_; lean_object* v_val_4603_; size_t v___x_4604_; size_t v___x_4605_; uint8_t v___x_4606_; 
v_key_4602_ = lean_ctor_get(v___x_4601_, 0);
v_val_4603_ = lean_ctor_get(v___x_4601_, 1);
v___x_4604_ = lean_ptr_addr(v_x_4595_);
v___x_4605_ = lean_ptr_addr(v_key_4602_);
v___x_4606_ = lean_usize_dec_eq(v___x_4604_, v___x_4605_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_box(0);
return v___x_4607_;
}
else
{
lean_object* v___x_4608_; 
lean_inc(v_val_4603_);
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_val_4603_);
return v___x_4608_;
}
}
case 1:
{
lean_object* v_node_4609_; size_t v___x_4610_; size_t v___x_4611_; 
v_node_4609_ = lean_ctor_get(v___x_4601_, 0);
v___x_4610_ = ((size_t)5ULL);
v___x_4611_ = lean_usize_shift_right(v_x_4594_, v___x_4610_);
v_x_4593_ = v_node_4609_;
v_x_4594_ = v___x_4611_;
goto _start;
}
default: 
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_box(0);
return v___x_4613_;
}
}
}
else
{
lean_object* v_ks_4614_; lean_object* v_vs_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v_ks_4614_ = lean_ctor_get(v_x_4593_, 0);
v_vs_4615_ = lean_ctor_get(v_x_4593_, 1);
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4614_, v_vs_4615_, v___x_4616_, v_x_4595_);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4618_, lean_object* v_x_4619_, lean_object* v_x_4620_){
_start:
{
size_t v_x_6741__boxed_4621_; lean_object* v_res_4622_; 
v_x_6741__boxed_4621_ = lean_unbox_usize(v_x_4619_);
lean_dec(v_x_4619_);
v_res_4622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4618_, v_x_6741__boxed_4621_, v_x_4620_);
lean_dec_ref(v_x_4620_);
lean_dec_ref(v_x_4618_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4623_, lean_object* v_x_4624_){
_start:
{
size_t v___x_4625_; size_t v___x_4626_; size_t v___x_4627_; uint64_t v___x_4628_; size_t v___x_4629_; lean_object* v___x_4630_; 
v___x_4625_ = lean_ptr_addr(v_x_4624_);
v___x_4626_ = ((size_t)3ULL);
v___x_4627_ = lean_usize_shift_right(v___x_4625_, v___x_4626_);
v___x_4628_ = lean_usize_to_uint64(v___x_4627_);
v___x_4629_ = lean_uint64_to_usize(v___x_4628_);
v___x_4630_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4623_, v___x_4629_, v_x_4624_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4631_, lean_object* v_x_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4631_, v_x_4632_);
lean_dec_ref(v_x_4632_);
lean_dec_ref(v_x_4631_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4637_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4716_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4649_ = v___x_4646_;
v_isShared_4650_ = v_isSharedCheck_4716_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4716_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
uint8_t v_linarith_4651_; 
v_linarith_4651_ = lean_ctor_get_uint8(v_a_4647_, sizeof(void*)*14 + 22);
lean_dec(v_a_4647_);
if (v_linarith_4651_ == 0)
{
lean_object* v___x_4652_; lean_object* v___x_4654_; 
lean_dec_ref(v_type_4634_);
v___x_4652_ = lean_box(0);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 0, v___x_4652_);
v___x_4654_ = v___x_4649_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
else
{
lean_object* v___x_4656_; 
lean_del_object(v___x_4649_);
lean_inc_ref(v_type_4634_);
v___x_4656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_4634_, v_a_4637_, v_a_4642_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4707_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4707_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4707_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_unbox(v_a_4657_);
lean_dec(v_a_4657_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
lean_del_object(v___x_4659_);
v___x_4662_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4635_, v_a_4643_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4694_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4665_ = v___x_4662_;
v_isShared_4666_ = v_isSharedCheck_4694_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4662_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4694_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v_typeIdOf_4667_; lean_object* v___x_4668_; 
v_typeIdOf_4667_ = lean_ctor_get(v_a_4663_, 1);
lean_inc_ref(v_typeIdOf_4667_);
lean_dec(v_a_4663_);
v___x_4668_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4667_, v_type_4634_);
lean_dec_ref(v_typeIdOf_4667_);
if (lean_obj_tag(v___x_4668_) == 1)
{
lean_object* v_val_4669_; lean_object* v___x_4671_; 
lean_dec_ref(v_type_4634_);
v_val_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_val_4669_);
lean_dec_ref_known(v___x_4668_, 1);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 0, v_val_4669_);
v___x_4671_ = v___x_4665_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_val_4669_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
else
{
lean_object* v___x_4673_; 
lean_dec(v___x_4668_);
lean_del_object(v___x_4665_);
lean_inc_ref(v_type_4634_);
v___x_4673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc_n(v_a_4674_, 2);
lean_dec_ref_known(v___x_4673_, 1);
v___f_4675_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4675_, 0, v_type_4634_);
lean_closure_set(v___f_4675_, 1, v_a_4674_);
v___x_4676_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4677_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4676_, v___f_4675_, v_a_4635_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v___x_4677_, 0);
lean_dec(v_unused_4685_);
v___x_4679_ = v___x_4677_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_dec(v___x_4677_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v_a_4674_);
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4674_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_a_4674_);
v_a_4686_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4677_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4677_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
else
{
lean_dec_ref(v_type_4634_);
return v___x_4673_;
}
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
lean_dec_ref(v_type_4634_);
v_a_4695_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4662_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4662_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4705_; 
lean_dec_ref(v_type_4634_);
v___x_4703_ = lean_box(0);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4703_);
v___x_4705_ = v___x_4659_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4703_);
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
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
lean_dec_ref(v_type_4634_);
v_a_4708_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4656_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4656_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec_ref(v_type_4634_);
v_a_4717_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4646_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4646_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec(v_a_4726_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4738_, lean_object* v_x_4739_, lean_object* v_x_4740_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4739_, v_x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4742_, lean_object* v_x_4743_, lean_object* v_x_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4742_, v_x_4743_, v_x_4744_);
lean_dec_ref(v_x_4744_);
lean_dec_ref(v_x_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4746_, lean_object* v_x_4747_, size_t v_x_4748_, lean_object* v_x_4749_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4747_, v_x_4748_, v_x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4751_, lean_object* v_x_4752_, lean_object* v_x_4753_, lean_object* v_x_4754_){
_start:
{
size_t v_x_6977__boxed_4755_; lean_object* v_res_4756_; 
v_x_6977__boxed_4755_ = lean_unbox_usize(v_x_4753_);
lean_dec(v_x_4753_);
v_res_4756_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4751_, v_x_4752_, v_x_6977__boxed_4755_, v_x_4754_);
lean_dec_ref(v_x_4754_);
lean_dec_ref(v_x_4752_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4757_, lean_object* v_keys_4758_, lean_object* v_vals_4759_, lean_object* v_heq_4760_, lean_object* v_i_4761_, lean_object* v_k_4762_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4758_, v_vals_4759_, v_i_4761_, v_k_4762_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4764_, lean_object* v_keys_4765_, lean_object* v_vals_4766_, lean_object* v_heq_4767_, lean_object* v_i_4768_, lean_object* v_k_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4764_, v_keys_4765_, v_vals_4766_, v_heq_4767_, v_i_4768_, v_k_4769_);
lean_dec_ref(v_k_4769_);
lean_dec_ref(v_vals_4766_);
lean_dec_ref(v_keys_4765_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4771_, lean_object* v_type_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4780_ = lean_box(0);
v___x_4781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4781_, 0, v_u_4771_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
v___x_4782_ = l_Lean_mkConst(v___x_4779_, v___x_4781_);
v___x_4783_ = l_Lean_Expr_app___override(v___x_4782_, v_type_4772_);
v___x_4784_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4783_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4785_, lean_object* v_type_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4785_, v_type_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
return v_res_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4794_, lean_object* v_type_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4794_, v_type_4795_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4808_, lean_object* v_type_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4808_, v_type_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec(v_a_4813_);
lean_dec_ref(v_a_4812_);
lean_dec(v_a_4811_);
lean_dec(v_a_4810_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4822_, lean_object* v_s_4823_){
_start:
{
lean_object* v_structs_4824_; lean_object* v_typeIdOf_4825_; lean_object* v_exprToStructId_4826_; lean_object* v_exprToStructIdEntries_4827_; lean_object* v_forbiddenNatModules_4828_; lean_object* v_natStructs_4829_; lean_object* v_natTypeIdOf_4830_; lean_object* v_exprToNatStructId_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4839_; 
v_structs_4824_ = lean_ctor_get(v_s_4823_, 0);
v_typeIdOf_4825_ = lean_ctor_get(v_s_4823_, 1);
v_exprToStructId_4826_ = lean_ctor_get(v_s_4823_, 2);
v_exprToStructIdEntries_4827_ = lean_ctor_get(v_s_4823_, 3);
v_forbiddenNatModules_4828_ = lean_ctor_get(v_s_4823_, 4);
v_natStructs_4829_ = lean_ctor_get(v_s_4823_, 5);
v_natTypeIdOf_4830_ = lean_ctor_get(v_s_4823_, 6);
v_exprToNatStructId_4831_ = lean_ctor_get(v_s_4823_, 7);
v_isSharedCheck_4839_ = !lean_is_exclusive(v_s_4823_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4833_ = v_s_4823_;
v_isShared_4834_ = v_isSharedCheck_4839_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_exprToNatStructId_4831_);
lean_inc(v_natTypeIdOf_4830_);
lean_inc(v_natStructs_4829_);
lean_inc(v_forbiddenNatModules_4828_);
lean_inc(v_exprToStructIdEntries_4827_);
lean_inc(v_exprToStructId_4826_);
lean_inc(v_typeIdOf_4825_);
lean_inc(v_structs_4824_);
lean_dec(v_s_4823_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4839_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4835_ = lean_array_push(v_natStructs_4829_, v___x_4822_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 5, v___x_4835_);
v___x_4837_ = v___x_4833_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_structs_4824_);
lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_typeIdOf_4825_);
lean_ctor_set(v_reuseFailAlloc_4838_, 2, v_exprToStructId_4826_);
lean_ctor_set(v_reuseFailAlloc_4838_, 3, v_exprToStructIdEntries_4827_);
lean_ctor_set(v_reuseFailAlloc_4838_, 4, v_forbiddenNatModules_4828_);
lean_ctor_set(v_reuseFailAlloc_4838_, 5, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4838_, 6, v_natTypeIdOf_4830_);
lean_ctor_set(v_reuseFailAlloc_4838_, 7, v_exprToNatStructId_4831_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_ref_4846_; lean_object* v___x_4847_; lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4856_; 
v_ref_4846_ = lean_ctor_get(v___y_4843_, 2);
v___x_4847_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4850_ = v___x_4847_;
v_isShared_4851_ = v_isSharedCheck_4856_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4847_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4856_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v___x_4854_; 
lean_inc(v_ref_4846_);
v___x_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4852_, 0, v_ref_4846_);
lean_ctor_set(v___x_4852_, 1, v_a_4848_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set_tag(v___x_4850_, 1);
lean_ctor_set(v___x_4850_, 0, v___x_4852_);
v___x_4854_ = v___x_4850_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
return v_res_4863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
v___x_4880_ = l_Lean_stringToMessageData(v___x_4879_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___x_4893_; 
lean_inc_ref(v_type_4881_);
v___x_4893_ = l_Lean_Meta_getDecLevel(v_type_4881_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4895_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc_n(v_a_4894_, 2);
lean_dec_ref_known(v___x_4893_, 1);
lean_inc_ref(v_type_4881_);
v___x_4895_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4894_, v_type_4881_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_5188_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_5188_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_5188_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
if (lean_obj_tag(v_a_4896_) == 1)
{
lean_object* v_val_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
lean_del_object(v___x_4898_);
v_val_4900_ = lean_ctor_get(v_a_4896_, 0);
lean_inc_n(v_val_4900_, 2);
lean_dec_ref_known(v_a_4896_, 1);
v___x_4901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4902_ = lean_box(0);
lean_inc(v_a_4894_);
v___x_4903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4903_, 0, v_a_4894_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
lean_inc_ref(v___x_4903_);
v___x_4904_ = l_Lean_mkConst(v___x_4901_, v___x_4903_);
lean_inc_ref(v_type_4881_);
v___x_4905_ = l_Lean_mkAppB(v___x_4904_, v_type_4881_, v_val_4900_);
v___x_4906_ = l_Lean_Meta_Sym_canon(v___x_4905_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4908_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___x_4906_, 1);
v___x_4908_ = l_Lean_Meta_Sym_shareCommon(v_a_4907_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4910_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc_n(v_a_4909_, 2);
lean_dec_ref_known(v___x_4908_, 1);
v___x_4910_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4909_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
if (lean_obj_tag(v_a_4911_) == 1)
{
lean_object* v_val_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_5163_; 
v_val_4912_ = lean_ctor_get(v_a_4911_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v_a_4911_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_4914_ = v_a_4911_;
v_isShared_4915_ = v_isSharedCheck_5163_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_val_4912_);
lean_dec(v_a_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_5163_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4916_, v_a_4894_, v_type_4881_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v___x_4919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4919_, v_a_4894_, v_type_4881_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
lean_inc(v_a_4918_);
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4922_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_4894_, v_type_4881_, v_a_4918_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4922_, 1);
lean_inc(v_a_4918_);
lean_inc(v_a_4921_);
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4924_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_4894_, v_type_4881_, v_a_4921_, v_a_4918_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v_a_4925_; lean_object* v___x_4926_; 
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_a_4925_);
lean_dec_ref_known(v___x_4924_, 1);
lean_inc(v_a_4918_);
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4926_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_4894_, v_type_4881_, v_a_4918_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_a_4927_);
lean_dec_ref_known(v___x_4926_, 1);
v___x_4928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4928_, v_a_4894_, v_type_4881_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc_n(v_a_4930_, 2);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4903_);
lean_inc_n(v_a_4894_, 2);
v___x_4932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4932_, 0, v_a_4894_);
lean_ctor_set(v___x_4932_, 1, v___x_4903_);
lean_inc_ref(v___x_4932_);
v___x_4933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4933_, 0, v_a_4894_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_mkConst(v___x_4931_, v___x_4933_);
lean_inc_ref_n(v_type_4881_, 3);
v___x_4935_ = l_Lean_mkApp4(v___x_4934_, v_type_4881_, v_type_4881_, v_type_4881_, v_a_4930_);
v___x_4936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4935_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v_orderedAddInst_x3f_4939_; lean_object* v___y_4940_; lean_object* v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
if (lean_obj_tag(v_a_4918_) == 1)
{
if (lean_obj_tag(v_a_4923_) == 1)
{
lean_object* v_val_5092_; lean_object* v_val_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v_val_5092_ = lean_ctor_get(v_a_4918_, 0);
v_val_5093_ = lean_ctor_get(v_a_4923_, 0);
v___x_5094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4903_);
v___x_5095_ = l_Lean_mkConst(v___x_5094_, v___x_4903_);
lean_inc(v_val_5093_);
lean_inc(v_val_5092_);
lean_inc_ref(v_type_4881_);
v___x_5096_ = l_Lean_mkApp4(v___x_5095_, v_type_4881_, v_a_4930_, v_val_5092_, v_val_5093_);
v___x_5097_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5096_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
v_orderedAddInst_x3f_4939_ = v_a_5098_;
v___y_4940_ = v_a_4882_;
v___y_4941_ = v_a_4883_;
v___y_4942_ = v_a_4884_;
v___y_4943_ = v_a_4885_;
v___y_4944_ = v_a_4886_;
v___y_4945_ = v_a_4887_;
v___y_4946_ = v_a_4888_;
v___y_4947_ = v_a_4889_;
v___y_4948_ = v_a_4890_;
v___y_4949_ = v_a_4891_;
goto v___jp_4938_;
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
lean_dec_ref_known(v_a_4923_, 1);
lean_dec_ref_known(v_a_4918_, 1);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4921_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5099_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v___x_5097_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5097_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
else
{
lean_dec(v_a_4930_);
v___y_5081_ = v_a_4882_;
v___y_5082_ = v_a_4883_;
v___y_5083_ = v_a_4884_;
v___y_5084_ = v_a_4885_;
v___y_5085_ = v_a_4886_;
v___y_5086_ = v_a_4887_;
v___y_5087_ = v_a_4888_;
v___y_5088_ = v_a_4889_;
v___y_5089_ = v_a_4890_;
v___y_5090_ = v_a_4891_;
goto v___jp_5080_;
}
}
else
{
lean_dec(v_a_4930_);
v___y_5081_ = v_a_4882_;
v___y_5082_ = v_a_4883_;
v___y_5083_ = v_a_4884_;
v___y_5084_ = v_a_4885_;
v___y_5085_ = v_a_4886_;
v___y_5086_ = v_a_4887_;
v___y_5087_ = v_a_4888_;
v___y_5088_ = v_a_4889_;
v___y_5089_ = v_a_4890_;
v___y_5090_ = v_a_4891_;
goto v___jp_5080_;
}
v___jp_4938_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4903_);
v___x_4951_ = l_Lean_mkConst(v___x_4950_, v___x_4903_);
lean_inc_ref(v_type_4881_);
v___x_4952_ = l_Lean_Expr_app___override(v___x_4951_, v_type_4881_);
v___x_4953_ = l_Lean_Meta_Sym_synthInstance(v___x_4952_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v_a_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
lean_inc(v_a_4954_);
lean_dec_ref_known(v___x_4953_, 1);
v___x_4955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4903_);
v___x_4956_ = l_Lean_mkConst(v___x_4955_, v___x_4903_);
lean_inc_ref(v_type_4881_);
v___x_4957_ = l_Lean_mkAppB(v___x_4956_, v_type_4881_, v_a_4954_);
v___x_4958_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4957_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4903_);
v___x_4961_ = l_Lean_mkConst(v___x_4960_, v___x_4903_);
lean_inc(v_val_4900_);
lean_inc_ref(v_type_4881_);
v___x_4962_ = l_Lean_mkAppB(v___x_4961_, v_type_4881_, v_val_4900_);
v___x_4963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4962_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v___x_4965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4966_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4965_, v_a_4894_, v_type_4881_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4966_, 1);
v___x_4968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_4969_ = l_Lean_mkConst(v___x_4968_, v___x_4903_);
lean_inc_ref(v_type_4881_);
v___x_4970_ = l_Lean_mkAppB(v___x_4969_, v_type_4881_, v_a_4967_);
v___x_4971_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4970_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4973_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref_known(v___x_4971_, 1);
lean_inc_ref(v_type_4881_);
lean_inc(v_a_4894_);
v___x_4973_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4894_, v_type_4881_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
v___x_4975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
lean_ctor_set(v___x_4977_, 1, v___x_4932_);
v___x_4978_ = l_Lean_mkConst(v___x_4975_, v___x_4977_);
v___x_4979_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4881_, 2);
v___x_4980_ = l_Lean_mkApp4(v___x_4978_, v___x_4979_, v_type_4881_, v_type_4881_, v_a_4974_);
v___x_4981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4980_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v___x_4983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4894_);
v___x_4984_ = l_Lean_Level_succ___override(v_a_4894_);
v___x_4985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
lean_ctor_set(v___x_4985_, 1, v___x_4902_);
v___x_4986_ = l_Lean_mkConst(v___x_4983_, v___x_4985_);
v___x_4987_ = l_Lean_Expr_app___override(v___x_4986_, v_a_4909_);
v___x_4988_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4940_, v___y_4948_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v_natStructs_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___f_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
v_natStructs_4990_ = lean_ctor_get(v_a_4989_, 5);
lean_inc_ref(v_natStructs_4990_);
lean_dec(v_a_4989_);
v___x_4991_ = lean_array_get_size(v_natStructs_4990_);
lean_dec_ref(v_natStructs_4990_);
v___x_4992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_4993_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set(v___x_4993_, 1, v_val_4912_);
lean_ctor_set(v___x_4993_, 2, v_type_4881_);
lean_ctor_set(v___x_4993_, 3, v_a_4894_);
lean_ctor_set(v___x_4993_, 4, v_val_4900_);
lean_ctor_set(v___x_4993_, 5, v_a_4918_);
lean_ctor_set(v___x_4993_, 6, v_a_4921_);
lean_ctor_set(v___x_4993_, 7, v_a_4925_);
lean_ctor_set(v___x_4993_, 8, v_a_4923_);
lean_ctor_set(v___x_4993_, 9, v_orderedAddInst_x3f_4939_);
lean_ctor_set(v___x_4993_, 10, v_a_4927_);
lean_ctor_set(v___x_4993_, 11, v_a_4959_);
lean_ctor_set(v___x_4993_, 12, v___x_4987_);
lean_ctor_set(v___x_4993_, 13, v_a_4972_);
lean_ctor_set(v___x_4993_, 14, v_a_4964_);
lean_ctor_set(v___x_4993_, 15, v_a_4937_);
lean_ctor_set(v___x_4993_, 16, v_a_4982_);
lean_ctor_set(v___x_4993_, 17, v___x_4992_);
v___f_4994_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4994_, 0, v___x_4993_);
v___x_4995_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4996_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4995_, v___f_4994_, v___y_4940_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5006_; 
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5006_ == 0)
{
lean_object* v_unused_5007_; 
v_unused_5007_ = lean_ctor_get(v___x_4996_, 0);
lean_dec(v_unused_5007_);
v___x_4998_ = v___x_4996_;
v_isShared_4999_ = v_isSharedCheck_5006_;
goto v_resetjp_4997_;
}
else
{
lean_dec(v___x_4996_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5006_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4991_);
v___x_5001_ = v___x_4914_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_4991_);
v___x_5001_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
lean_object* v___x_5003_; 
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 0, v___x_5001_);
v___x_5003_ = v___x_4998_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_del_object(v___x_4914_);
v_a_5008_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4996_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4996_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref(v___x_4987_);
lean_dec(v_a_4982_);
lean_dec(v_a_4972_);
lean_dec(v_a_4964_);
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5016_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_4988_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4988_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_a_4972_);
lean_dec(v_a_4964_);
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5024_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_4981_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_4981_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec(v_a_4972_);
lean_dec(v_a_4964_);
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5032_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_4973_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_4973_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_a_4964_);
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5040_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_4971_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_4971_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec(v_a_4964_);
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5048_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_4966_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_4966_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec(v_a_4959_);
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5056_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_4963_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_4963_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5064_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_4958_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_4958_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec(v_orderedAddInst_x3f_4939_);
lean_dec(v_a_4937_);
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5072_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_4953_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_4953_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
v___jp_5080_:
{
lean_object* v___x_5091_; 
v___x_5091_ = lean_box(0);
v_orderedAddInst_x3f_4939_ = v___x_5091_;
v___y_4940_ = v___y_5081_;
v___y_4941_ = v___y_5082_;
v___y_4942_ = v___y_5083_;
v___y_4943_ = v___y_5084_;
v___y_4944_ = v___y_5085_;
v___y_4945_ = v___y_5086_;
v___y_4946_ = v___y_5087_;
v___y_4947_ = v___y_5088_;
v___y_4948_ = v___y_5089_;
v___y_4949_ = v___y_5090_;
goto v___jp_4938_;
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec_ref_known(v___x_4932_, 2);
lean_dec(v_a_4930_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5107_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_4936_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_4936_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5115_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_4929_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_4929_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5123_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_4926_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_4926_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
else
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5138_; 
lean_dec(v_a_4923_);
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5131_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5133_ = v___x_4924_;
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_4924_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5136_; 
if (v_isShared_5134_ == 0)
{
v___x_5136_ = v___x_5133_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec(v_a_4921_);
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5139_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_4922_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_4922_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec(v_a_4918_);
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5147_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_4920_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_4920_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_del_object(v___x_4914_);
lean_dec(v_val_4912_);
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5155_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_4917_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_4917_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v___x_5164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7);
v___x_5165_ = l_Lean_indentExpr(v_a_4909_);
v___x_5166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5164_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5166_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
return v___x_5167_;
}
}
else
{
lean_dec(v_a_4909_);
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
return v___x_4910_;
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5168_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_4908_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_4908_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
lean_dec_ref_known(v___x_4903_, 2);
lean_dec(v_val_4900_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5176_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_4906_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_4906_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
else
{
lean_object* v___x_5184_; lean_object* v___x_5186_; 
lean_dec(v_a_4896_);
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v___x_5184_ = lean_box(0);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_5184_);
v___x_5186_ = v___x_4898_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5184_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
lean_dec(v_a_4894_);
lean_dec_ref(v_type_4881_);
v_a_5189_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_4895_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_4895_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec_ref(v_type_4881_);
v_a_5197_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_4893_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_4893_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec(v_a_5211_);
lean_dec_ref(v_a_5210_);
lean_dec(v_a_5209_);
lean_dec_ref(v_a_5208_);
lean_dec(v_a_5207_);
lean_dec(v_a_5206_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5218_, lean_object* v_msg_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5219_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5232_, lean_object* v_msg_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5232_, v_msg_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec(v___y_5234_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5246_, lean_object* v_a_5247_, lean_object* v_s_5248_){
_start:
{
lean_object* v_structs_5249_; lean_object* v_typeIdOf_5250_; lean_object* v_exprToStructId_5251_; lean_object* v_exprToStructIdEntries_5252_; lean_object* v_forbiddenNatModules_5253_; lean_object* v_natStructs_5254_; lean_object* v_natTypeIdOf_5255_; lean_object* v_exprToNatStructId_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5264_; 
v_structs_5249_ = lean_ctor_get(v_s_5248_, 0);
v_typeIdOf_5250_ = lean_ctor_get(v_s_5248_, 1);
v_exprToStructId_5251_ = lean_ctor_get(v_s_5248_, 2);
v_exprToStructIdEntries_5252_ = lean_ctor_get(v_s_5248_, 3);
v_forbiddenNatModules_5253_ = lean_ctor_get(v_s_5248_, 4);
v_natStructs_5254_ = lean_ctor_get(v_s_5248_, 5);
v_natTypeIdOf_5255_ = lean_ctor_get(v_s_5248_, 6);
v_exprToNatStructId_5256_ = lean_ctor_get(v_s_5248_, 7);
v_isSharedCheck_5264_ = !lean_is_exclusive(v_s_5248_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5258_ = v_s_5248_;
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_exprToNatStructId_5256_);
lean_inc(v_natTypeIdOf_5255_);
lean_inc(v_natStructs_5254_);
lean_inc(v_forbiddenNatModules_5253_);
lean_inc(v_exprToStructIdEntries_5252_);
lean_inc(v_exprToStructId_5251_);
lean_inc(v_typeIdOf_5250_);
lean_inc(v_structs_5249_);
lean_dec(v_s_5248_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5255_, v_type_5246_, v_a_5247_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 6, v___x_5260_);
v___x_5262_ = v___x_5258_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_structs_5249_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_typeIdOf_5250_);
lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_exprToStructId_5251_);
lean_ctor_set(v_reuseFailAlloc_5263_, 3, v_exprToStructIdEntries_5252_);
lean_ctor_set(v_reuseFailAlloc_5263_, 4, v_forbiddenNatModules_5253_);
lean_ctor_set(v_reuseFailAlloc_5263_, 5, v_natStructs_5254_);
lean_ctor_set(v_reuseFailAlloc_5263_, 6, v___x_5260_);
lean_ctor_set(v_reuseFailAlloc_5263_, 7, v_exprToNatStructId_5256_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5265_, lean_object* v_i_5266_, lean_object* v_k_5267_){
_start:
{
lean_object* v___x_5268_; uint8_t v___x_5269_; 
v___x_5268_ = lean_array_get_size(v_keys_5265_);
v___x_5269_ = lean_nat_dec_lt(v_i_5266_, v___x_5268_);
if (v___x_5269_ == 0)
{
lean_dec(v_i_5266_);
return v___x_5269_;
}
else
{
lean_object* v_k_x27_5270_; size_t v___x_5271_; size_t v___x_5272_; uint8_t v___x_5273_; 
v_k_x27_5270_ = lean_array_fget_borrowed(v_keys_5265_, v_i_5266_);
v___x_5271_ = lean_ptr_addr(v_k_5267_);
v___x_5272_ = lean_ptr_addr(v_k_x27_5270_);
v___x_5273_ = lean_usize_dec_eq(v___x_5271_, v___x_5272_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_unsigned_to_nat(1u);
v___x_5275_ = lean_nat_add(v_i_5266_, v___x_5274_);
lean_dec(v_i_5266_);
v_i_5266_ = v___x_5275_;
goto _start;
}
else
{
lean_dec(v_i_5266_);
return v___x_5269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5277_, lean_object* v_i_5278_, lean_object* v_k_5279_){
_start:
{
uint8_t v_res_5280_; lean_object* v_r_5281_; 
v_res_5280_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5277_, v_i_5278_, v_k_5279_);
lean_dec_ref(v_k_5279_);
lean_dec_ref(v_keys_5277_);
v_r_5281_ = lean_box(v_res_5280_);
return v_r_5281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5282_, size_t v_x_5283_, lean_object* v_x_5284_){
_start:
{
if (lean_obj_tag(v_x_5282_) == 0)
{
lean_object* v_es_5285_; lean_object* v___x_5286_; size_t v___x_5287_; size_t v___x_5288_; lean_object* v_j_5289_; lean_object* v___x_5290_; 
v_es_5285_ = lean_ctor_get(v_x_5282_, 0);
v___x_5286_ = lean_box(2);
v___x_5287_ = ((size_t)31ULL);
v___x_5288_ = lean_usize_land(v_x_5283_, v___x_5287_);
v_j_5289_ = lean_usize_to_nat(v___x_5288_);
v___x_5290_ = lean_array_get_borrowed(v___x_5286_, v_es_5285_, v_j_5289_);
lean_dec(v_j_5289_);
switch(lean_obj_tag(v___x_5290_))
{
case 0:
{
lean_object* v_key_5291_; size_t v___x_5292_; size_t v___x_5293_; uint8_t v___x_5294_; 
v_key_5291_ = lean_ctor_get(v___x_5290_, 0);
v___x_5292_ = lean_ptr_addr(v_x_5284_);
v___x_5293_ = lean_ptr_addr(v_key_5291_);
v___x_5294_ = lean_usize_dec_eq(v___x_5292_, v___x_5293_);
return v___x_5294_;
}
case 1:
{
lean_object* v_node_5295_; size_t v___x_5296_; size_t v___x_5297_; 
v_node_5295_ = lean_ctor_get(v___x_5290_, 0);
v___x_5296_ = ((size_t)5ULL);
v___x_5297_ = lean_usize_shift_right(v_x_5283_, v___x_5296_);
v_x_5282_ = v_node_5295_;
v_x_5283_ = v___x_5297_;
goto _start;
}
default: 
{
uint8_t v___x_5299_; 
v___x_5299_ = 0;
return v___x_5299_;
}
}
}
else
{
lean_object* v_ks_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v_ks_5300_ = lean_ctor_get(v_x_5282_, 0);
v___x_5301_ = lean_unsigned_to_nat(0u);
v___x_5302_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5300_, v___x_5301_, v_x_5284_);
return v___x_5302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5303_, lean_object* v_x_5304_, lean_object* v_x_5305_){
_start:
{
size_t v_x_8678__boxed_5306_; uint8_t v_res_5307_; lean_object* v_r_5308_; 
v_x_8678__boxed_5306_ = lean_unbox_usize(v_x_5304_);
lean_dec(v_x_5304_);
v_res_5307_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5303_, v_x_8678__boxed_5306_, v_x_5305_);
lean_dec_ref(v_x_5305_);
lean_dec_ref(v_x_5303_);
v_r_5308_ = lean_box(v_res_5307_);
return v_r_5308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5309_, lean_object* v_x_5310_){
_start:
{
size_t v___x_5311_; size_t v___x_5312_; size_t v___x_5313_; uint64_t v___x_5314_; size_t v___x_5315_; uint8_t v___x_5316_; 
v___x_5311_ = lean_ptr_addr(v_x_5310_);
v___x_5312_ = ((size_t)3ULL);
v___x_5313_ = lean_usize_shift_right(v___x_5311_, v___x_5312_);
v___x_5314_ = lean_usize_to_uint64(v___x_5313_);
v___x_5315_ = lean_uint64_to_usize(v___x_5314_);
v___x_5316_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5309_, v___x_5315_, v_x_5310_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5317_, lean_object* v_x_5318_){
_start:
{
uint8_t v_res_5319_; lean_object* v_r_5320_; 
v_res_5319_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5317_, v_x_5318_);
lean_dec_ref(v_x_5318_);
lean_dec_ref(v_x_5317_);
v_r_5320_ = lean_box(v_res_5319_);
return v_r_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v___x_5333_; 
v___x_5333_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5324_);
if (lean_obj_tag(v___x_5333_) == 0)
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5423_; 
v_a_5334_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5336_ = v___x_5333_;
v_isShared_5337_ = v_isSharedCheck_5423_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5333_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5423_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
uint8_t v_linarith_5338_; 
v_linarith_5338_ = lean_ctor_get_uint8(v_a_5334_, sizeof(void*)*14 + 22);
lean_dec(v_a_5334_);
if (v_linarith_5338_ == 0)
{
lean_object* v___x_5339_; lean_object* v___x_5341_; 
lean_dec_ref(v_type_5321_);
v___x_5339_ = lean_box(0);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 0, v___x_5339_);
v___x_5341_ = v___x_5336_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5339_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
else
{
lean_object* v___x_5343_; 
lean_del_object(v___x_5336_);
v___x_5343_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5322_, v_a_5330_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5414_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5346_ = v___x_5343_;
v_isShared_5347_ = v_isSharedCheck_5414_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5343_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5414_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v_forbiddenNatModules_5348_; uint8_t v___x_5349_; 
v_forbiddenNatModules_5348_ = lean_ctor_get(v_a_5344_, 4);
lean_inc_ref(v_forbiddenNatModules_5348_);
lean_dec(v_a_5344_);
v___x_5349_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5348_, v_type_5321_);
lean_dec_ref(v_forbiddenNatModules_5348_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; 
lean_del_object(v___x_5346_);
lean_inc_ref(v_type_5321_);
v___x_5350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_5321_, v_a_5324_, v_a_5329_);
if (lean_obj_tag(v___x_5350_) == 0)
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5401_; 
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5353_ = v___x_5350_;
v_isShared_5354_ = v_isSharedCheck_5401_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5350_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5401_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
uint8_t v___x_5355_; 
v___x_5355_ = lean_unbox(v_a_5351_);
lean_dec(v_a_5351_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; 
lean_del_object(v___x_5353_);
v___x_5356_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5322_, v_a_5330_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5388_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5359_ = v___x_5356_;
v_isShared_5360_ = v_isSharedCheck_5388_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5356_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5388_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v_natTypeIdOf_5361_; lean_object* v___x_5362_; 
v_natTypeIdOf_5361_ = lean_ctor_get(v_a_5357_, 6);
lean_inc_ref(v_natTypeIdOf_5361_);
lean_dec(v_a_5357_);
v___x_5362_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5361_, v_type_5321_);
lean_dec_ref(v_natTypeIdOf_5361_);
if (lean_obj_tag(v___x_5362_) == 1)
{
lean_object* v_val_5363_; lean_object* v___x_5365_; 
lean_dec_ref(v_type_5321_);
v_val_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_val_5363_);
lean_dec_ref_known(v___x_5362_, 1);
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 0, v_val_5363_);
v___x_5365_ = v___x_5359_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_val_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
else
{
lean_object* v___x_5367_; 
lean_dec(v___x_5362_);
lean_del_object(v___x_5359_);
lean_inc_ref(v_type_5321_);
v___x_5367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_);
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; lean_object* v___f_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
lean_inc_n(v_a_5368_, 2);
lean_dec_ref_known(v___x_5367_, 1);
v___f_5369_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5369_, 0, v_type_5321_);
lean_closure_set(v___f_5369_, 1, v_a_5368_);
v___x_5370_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5371_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5370_, v___f_5369_, v_a_5322_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5378_ == 0)
{
lean_object* v_unused_5379_; 
v_unused_5379_ = lean_ctor_get(v___x_5371_, 0);
lean_dec(v_unused_5379_);
v___x_5373_ = v___x_5371_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_dec(v___x_5371_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 0, v_a_5368_);
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5368_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
else
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5387_; 
lean_dec(v_a_5368_);
v_a_5380_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5382_ = v___x_5371_;
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5371_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5385_; 
if (v_isShared_5383_ == 0)
{
v___x_5385_ = v___x_5382_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
}
else
{
lean_dec_ref(v_type_5321_);
return v___x_5367_;
}
}
}
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec_ref(v_type_5321_);
v_a_5389_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5356_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5356_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5399_; 
lean_dec_ref(v_type_5321_);
v___x_5397_ = lean_box(0);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 0, v___x_5397_);
v___x_5399_ = v___x_5353_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec_ref(v_type_5321_);
v_a_5402_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5350_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5350_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
else
{
lean_object* v___x_5410_; lean_object* v___x_5412_; 
lean_dec_ref(v_type_5321_);
v___x_5410_ = lean_box(0);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 0, v___x_5410_);
v___x_5412_ = v___x_5346_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec_ref(v_type_5321_);
v_a_5415_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5343_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5343_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v_type_5321_);
v_a_5424_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5333_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5333_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec_ref(v_a_5439_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec(v_a_5433_);
return v_res_5444_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5445_, lean_object* v_x_5446_, lean_object* v_x_5447_){
_start:
{
uint8_t v___x_5448_; 
v___x_5448_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5446_, v_x_5447_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5449_, lean_object* v_x_5450_, lean_object* v_x_5451_){
_start:
{
uint8_t v_res_5452_; lean_object* v_r_5453_; 
v_res_5452_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5449_, v_x_5450_, v_x_5451_);
lean_dec_ref(v_x_5451_);
lean_dec_ref(v_x_5450_);
v_r_5453_ = lean_box(v_res_5452_);
return v_r_5453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5454_, lean_object* v_x_5455_, size_t v_x_5456_, lean_object* v_x_5457_){
_start:
{
uint8_t v___x_5458_; 
v___x_5458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5455_, v_x_5456_, v_x_5457_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5459_, lean_object* v_x_5460_, lean_object* v_x_5461_, lean_object* v_x_5462_){
_start:
{
size_t v_x_8946__boxed_5463_; uint8_t v_res_5464_; lean_object* v_r_5465_; 
v_x_8946__boxed_5463_ = lean_unbox_usize(v_x_5461_);
lean_dec(v_x_5461_);
v_res_5464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5459_, v_x_5460_, v_x_8946__boxed_5463_, v_x_5462_);
lean_dec_ref(v_x_5462_);
lean_dec_ref(v_x_5460_);
v_r_5465_ = lean_box(v_res_5464_);
return v_r_5465_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5466_, lean_object* v_keys_5467_, lean_object* v_vals_5468_, lean_object* v_heq_5469_, lean_object* v_i_5470_, lean_object* v_k_5471_){
_start:
{
uint8_t v___x_5472_; 
v___x_5472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5467_, v_i_5470_, v_k_5471_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5473_, lean_object* v_keys_5474_, lean_object* v_vals_5475_, lean_object* v_heq_5476_, lean_object* v_i_5477_, lean_object* v_k_5478_){
_start:
{
uint8_t v_res_5479_; lean_object* v_r_5480_; 
v_res_5479_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5473_, v_keys_5474_, v_vals_5475_, v_heq_5476_, v_i_5477_, v_k_5478_);
lean_dec_ref(v_k_5478_);
lean_dec_ref(v_vals_5475_);
lean_dec_ref(v_keys_5474_);
v_r_5480_ = lean_box(v_res_5479_);
return v_r_5480_;
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
