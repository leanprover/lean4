// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Insts import Init.Grind.Module.Envelope
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; lean_object* v_mctx_231_; lean_object* v_lctx_232_; lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = lean_st_ref_get(v___y_224_);
v_mctx_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_mctx_231_);
lean_dec(v___x_230_);
v_lctx_232_ = lean_ctor_get(v___y_223_, 2);
v_options_233_ = lean_ctor_get(v___y_225_, 2);
lean_inc_ref(v_options_233_);
lean_inc_ref(v_lctx_232_);
v___x_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_234_, 0, v_env_229_);
lean_ctor_set(v___x_234_, 1, v_mctx_231_);
lean_ctor_set(v___x_234_, 2, v_lctx_232_);
lean_ctor_set(v___x_234_, 3, v_options_233_);
v___x_235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_msgData_222_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_ref_250_ = lean_ctor_get(v___y_247_, 5);
v___x_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
lean_inc(v_ref_250_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_ref_250_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc_ref(v_b_269_);
lean_inc_ref(v_a_268_);
v___x_275_ = l_Lean_Meta_isDefEqD(v_a_268_, v_b_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_288_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_288_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_288_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_288_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
uint8_t v___x_280_; 
v___x_280_ = lean_unbox(v_a_276_);
lean_dec(v_a_276_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v_a_282_; lean_object* v___x_283_; 
lean_del_object(v___x_278_);
v___x_281_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_268_, v_b_269_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref(v___x_281_);
v___x_283_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_a_282_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec_ref(v_b_269_);
lean_dec_ref(v_a_268_);
v___x_284_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_284_);
v___x_286_ = v___x_278_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_b_269_);
lean_dec_ref(v_a_268_);
v_a_289_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_275_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_275_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_297_, v_b_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* v_00_u03b1_305_, lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* v_00_u03b1_313_, lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(v_00_u03b1_313_, v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* v_p_321_, lean_object* v_x_322_, size_t v_x_323_, size_t v_x_324_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_cs_325_; size_t v_j_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_cs_325_ = lean_ctor_get(v_x_322_, 0);
v_j_326_ = lean_usize_shift_right(v_x_323_, v_x_324_);
v___x_327_ = lean_usize_to_nat(v_j_326_);
v___x_328_ = lean_array_get_size(v_cs_325_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v___x_327_);
lean_dec(v_p_321_);
return v_x_322_;
}
else
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_347_; 
lean_inc_ref(v_cs_325_);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_x_322_, 0);
lean_dec(v_unused_348_);
v___x_331_ = v_x_322_;
v_isShared_332_ = v_isSharedCheck_347_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_x_322_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_347_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v_i_336_; size_t v___x_337_; size_t v_shift_338_; lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_xs_x27_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_shift_left(v___x_333_, v_x_324_);
v___x_335_ = lean_usize_sub(v___x_334_, v___x_333_);
v_i_336_ = lean_usize_land(v_x_323_, v___x_335_);
v___x_337_ = ((size_t)5ULL);
v_shift_338_ = lean_usize_sub(v_x_324_, v___x_337_);
v_v_339_ = lean_array_fget(v_cs_325_, v___x_327_);
v___x_340_ = lean_box(0);
v_xs_x27_341_ = lean_array_fset(v_cs_325_, v___x_327_, v___x_340_);
v___x_342_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_321_, v_v_339_, v_i_336_, v_shift_338_);
v___x_343_ = lean_array_fset(v_xs_x27_341_, v___x_327_, v___x_342_);
lean_dec(v___x_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_343_);
v___x_345_ = v___x_331_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_vs_349_ = lean_ctor_get(v_x_322_, 0);
v___x_350_ = lean_usize_to_nat(v_x_323_);
v___x_351_ = lean_array_get_size(v_vs_349_);
v___x_352_ = lean_nat_dec_lt(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v___x_350_);
lean_dec(v_p_321_);
return v_x_322_;
}
else
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_vs_349_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_x_322_, 0);
lean_dec(v_unused_367_);
v___x_354_ = v_x_322_;
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_x_322_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_v_356_; lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v_v_356_ = lean_array_fget(v_vs_349_, v___x_350_);
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_vs_349_, v___x_350_, v___x_357_);
v___x_359_ = lean_box(9);
v___x_360_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_360_, 0, v_p_321_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*2, v___x_352_);
v___x_361_ = l_Lean_PersistentArray_push___redArg(v_v_356_, v___x_360_);
v___x_362_ = lean_array_fset(v_xs_x27_358_, v___x_350_, v___x_361_);
lean_dec(v___x_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_362_);
v___x_364_ = v___x_354_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* v_p_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
size_t v_x_269__boxed_372_; size_t v_x_270__boxed_373_; lean_object* v_res_374_; 
v_x_269__boxed_372_ = lean_unbox_usize(v_x_370_);
lean_dec(v_x_370_);
v_x_270__boxed_373_ = lean_unbox_usize(v_x_371_);
lean_dec(v_x_371_);
v_res_374_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_368_, v_x_369_, v_x_269__boxed_372_, v_x_270__boxed_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* v_p_375_, lean_object* v_t_376_, lean_object* v_i_377_){
_start:
{
lean_object* v_root_378_; lean_object* v_tail_379_; lean_object* v_size_380_; size_t v_shift_381_; lean_object* v_tailOff_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_408_; 
v_root_378_ = lean_ctor_get(v_t_376_, 0);
v_tail_379_ = lean_ctor_get(v_t_376_, 1);
v_size_380_ = lean_ctor_get(v_t_376_, 2);
v_shift_381_ = lean_ctor_get_usize(v_t_376_, 4);
v_tailOff_382_ = lean_ctor_get(v_t_376_, 3);
v_isSharedCheck_408_ = !lean_is_exclusive(v_t_376_);
if (v_isSharedCheck_408_ == 0)
{
v___x_384_ = v_t_376_;
v_isShared_385_ = v_isSharedCheck_408_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_tailOff_382_);
lean_inc(v_size_380_);
lean_inc(v_tail_379_);
lean_inc(v_root_378_);
lean_dec(v_t_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_408_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_le(v_tailOff_382_, v_i_377_);
if (v___x_386_ == 0)
{
size_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_usize_of_nat(v_i_377_);
v___x_388_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_375_, v_root_378_, v___x_387_, v_shift_381_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_388_);
v___x_390_ = v___x_384_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_tail_379_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_size_380_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_tailOff_382_);
lean_ctor_set_usize(v_reuseFailAlloc_391_, 4, v_shift_381_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_392_ = lean_nat_sub(v_i_377_, v_tailOff_382_);
v___x_393_ = lean_array_get_size(v_tail_379_);
v___x_394_ = lean_nat_dec_lt(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_396_; 
lean_dec(v___x_392_);
lean_dec(v_p_375_);
if (v_isShared_385_ == 0)
{
v___x_396_ = v___x_384_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_root_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_tail_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_size_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_tailOff_382_);
lean_ctor_set_usize(v_reuseFailAlloc_397_, 4, v_shift_381_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
else
{
lean_object* v_v_398_; lean_object* v___x_399_; lean_object* v_xs_x27_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v_v_398_ = lean_array_fget(v_tail_379_, v___x_392_);
v___x_399_ = lean_box(0);
v_xs_x27_400_ = lean_array_fset(v_tail_379_, v___x_392_, v___x_399_);
v___x_401_ = lean_box(9);
v___x_402_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_402_, 0, v_p_375_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*2, v___x_394_);
v___x_403_ = l_Lean_PersistentArray_push___redArg(v_v_398_, v___x_402_);
v___x_404_ = lean_array_fset(v_xs_x27_400_, v___x_392_, v___x_403_);
lean_dec(v___x_392_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v___x_404_);
v___x_406_ = v___x_384_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_root_378_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_size_380_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_tailOff_382_);
lean_ctor_set_usize(v_reuseFailAlloc_407_, 4, v_shift_381_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* v_p_409_, lean_object* v_t_410_, lean_object* v_i_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_409_, v_t_410_, v_i_411_);
lean_dec(v_i_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* v_a_413_, lean_object* v_p_414_, lean_object* v_one_415_, lean_object* v_s_416_){
_start:
{
lean_object* v_structs_417_; lean_object* v_typeIdOf_418_; lean_object* v_exprToStructId_419_; lean_object* v_exprToStructIdEntries_420_; lean_object* v_forbiddenNatModules_421_; lean_object* v_natStructs_422_; lean_object* v_natTypeIdOf_423_; lean_object* v_exprToNatStructId_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_structs_417_ = lean_ctor_get(v_s_416_, 0);
v_typeIdOf_418_ = lean_ctor_get(v_s_416_, 1);
v_exprToStructId_419_ = lean_ctor_get(v_s_416_, 2);
v_exprToStructIdEntries_420_ = lean_ctor_get(v_s_416_, 3);
v_forbiddenNatModules_421_ = lean_ctor_get(v_s_416_, 4);
v_natStructs_422_ = lean_ctor_get(v_s_416_, 5);
v_natTypeIdOf_423_ = lean_ctor_get(v_s_416_, 6);
v_exprToNatStructId_424_ = lean_ctor_get(v_s_416_, 7);
v___x_425_ = lean_array_get_size(v_structs_417_);
v___x_426_ = lean_nat_dec_lt(v_a_413_, v___x_425_);
if (v___x_426_ == 0)
{
lean_dec(v_p_414_);
return v_s_416_;
}
else
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_488_; 
lean_inc_ref(v_exprToNatStructId_424_);
lean_inc_ref(v_natTypeIdOf_423_);
lean_inc_ref(v_natStructs_422_);
lean_inc_ref(v_forbiddenNatModules_421_);
lean_inc_ref(v_exprToStructIdEntries_420_);
lean_inc_ref(v_exprToStructId_419_);
lean_inc_ref(v_typeIdOf_418_);
lean_inc_ref(v_structs_417_);
v_isSharedCheck_488_ = !lean_is_exclusive(v_s_416_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_489_ = lean_ctor_get(v_s_416_, 7);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_s_416_, 6);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_s_416_, 5);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_s_416_, 4);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_s_416_, 3);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_s_416_, 2);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_s_416_, 1);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_s_416_, 0);
lean_dec(v_unused_496_);
v___x_428_ = v_s_416_;
v_isShared_429_ = v_isSharedCheck_488_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_s_416_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_488_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_v_430_; lean_object* v_id_431_; lean_object* v_ringId_x3f_432_; lean_object* v_type_433_; lean_object* v_u_434_; lean_object* v_intModuleInst_435_; lean_object* v_leInst_x3f_436_; lean_object* v_ltInst_x3f_437_; lean_object* v_lawfulOrderLTInst_x3f_438_; lean_object* v_isPreorderInst_x3f_439_; lean_object* v_orderedAddInst_x3f_440_; lean_object* v_isLinearInst_x3f_441_; lean_object* v_noNatDivInst_x3f_442_; lean_object* v_ringInst_x3f_443_; lean_object* v_commRingInst_x3f_444_; lean_object* v_orderedRingInst_x3f_445_; lean_object* v_fieldInst_x3f_446_; lean_object* v_charInst_x3f_447_; lean_object* v_zero_448_; lean_object* v_ofNatZero_449_; lean_object* v_one_x3f_450_; lean_object* v_leFn_x3f_451_; lean_object* v_ltFn_x3f_452_; lean_object* v_addFn_453_; lean_object* v_zsmulFn_454_; lean_object* v_nsmulFn_455_; lean_object* v_zsmulFn_x3f_456_; lean_object* v_nsmulFn_x3f_457_; lean_object* v_homomulFn_x3f_458_; lean_object* v_subFn_459_; lean_object* v_negFn_460_; lean_object* v_vars_461_; lean_object* v_varMap_462_; lean_object* v_lowers_463_; lean_object* v_uppers_464_; lean_object* v_diseqs_465_; lean_object* v_assignment_466_; uint8_t v_caseSplits_467_; lean_object* v_conflict_x3f_468_; lean_object* v_diseqSplits_469_; lean_object* v_elimEqs_470_; lean_object* v_elimStack_471_; lean_object* v_occurs_472_; lean_object* v_ignored_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_487_; 
v_v_430_ = lean_array_fget(v_structs_417_, v_a_413_);
v_id_431_ = lean_ctor_get(v_v_430_, 0);
v_ringId_x3f_432_ = lean_ctor_get(v_v_430_, 1);
v_type_433_ = lean_ctor_get(v_v_430_, 2);
v_u_434_ = lean_ctor_get(v_v_430_, 3);
v_intModuleInst_435_ = lean_ctor_get(v_v_430_, 4);
v_leInst_x3f_436_ = lean_ctor_get(v_v_430_, 5);
v_ltInst_x3f_437_ = lean_ctor_get(v_v_430_, 6);
v_lawfulOrderLTInst_x3f_438_ = lean_ctor_get(v_v_430_, 7);
v_isPreorderInst_x3f_439_ = lean_ctor_get(v_v_430_, 8);
v_orderedAddInst_x3f_440_ = lean_ctor_get(v_v_430_, 9);
v_isLinearInst_x3f_441_ = lean_ctor_get(v_v_430_, 10);
v_noNatDivInst_x3f_442_ = lean_ctor_get(v_v_430_, 11);
v_ringInst_x3f_443_ = lean_ctor_get(v_v_430_, 12);
v_commRingInst_x3f_444_ = lean_ctor_get(v_v_430_, 13);
v_orderedRingInst_x3f_445_ = lean_ctor_get(v_v_430_, 14);
v_fieldInst_x3f_446_ = lean_ctor_get(v_v_430_, 15);
v_charInst_x3f_447_ = lean_ctor_get(v_v_430_, 16);
v_zero_448_ = lean_ctor_get(v_v_430_, 17);
v_ofNatZero_449_ = lean_ctor_get(v_v_430_, 18);
v_one_x3f_450_ = lean_ctor_get(v_v_430_, 19);
v_leFn_x3f_451_ = lean_ctor_get(v_v_430_, 20);
v_ltFn_x3f_452_ = lean_ctor_get(v_v_430_, 21);
v_addFn_453_ = lean_ctor_get(v_v_430_, 22);
v_zsmulFn_454_ = lean_ctor_get(v_v_430_, 23);
v_nsmulFn_455_ = lean_ctor_get(v_v_430_, 24);
v_zsmulFn_x3f_456_ = lean_ctor_get(v_v_430_, 25);
v_nsmulFn_x3f_457_ = lean_ctor_get(v_v_430_, 26);
v_homomulFn_x3f_458_ = lean_ctor_get(v_v_430_, 27);
v_subFn_459_ = lean_ctor_get(v_v_430_, 28);
v_negFn_460_ = lean_ctor_get(v_v_430_, 29);
v_vars_461_ = lean_ctor_get(v_v_430_, 30);
v_varMap_462_ = lean_ctor_get(v_v_430_, 31);
v_lowers_463_ = lean_ctor_get(v_v_430_, 32);
v_uppers_464_ = lean_ctor_get(v_v_430_, 33);
v_diseqs_465_ = lean_ctor_get(v_v_430_, 34);
v_assignment_466_ = lean_ctor_get(v_v_430_, 35);
v_caseSplits_467_ = lean_ctor_get_uint8(v_v_430_, sizeof(void*)*42);
v_conflict_x3f_468_ = lean_ctor_get(v_v_430_, 36);
v_diseqSplits_469_ = lean_ctor_get(v_v_430_, 37);
v_elimEqs_470_ = lean_ctor_get(v_v_430_, 38);
v_elimStack_471_ = lean_ctor_get(v_v_430_, 39);
v_occurs_472_ = lean_ctor_get(v_v_430_, 40);
v_ignored_473_ = lean_ctor_get(v_v_430_, 41);
v_isSharedCheck_487_ = !lean_is_exclusive(v_v_430_);
if (v_isSharedCheck_487_ == 0)
{
v___x_475_ = v_v_430_;
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_ignored_473_);
lean_inc(v_occurs_472_);
lean_inc(v_elimStack_471_);
lean_inc(v_elimEqs_470_);
lean_inc(v_diseqSplits_469_);
lean_inc(v_conflict_x3f_468_);
lean_inc(v_assignment_466_);
lean_inc(v_diseqs_465_);
lean_inc(v_uppers_464_);
lean_inc(v_lowers_463_);
lean_inc(v_varMap_462_);
lean_inc(v_vars_461_);
lean_inc(v_negFn_460_);
lean_inc(v_subFn_459_);
lean_inc(v_homomulFn_x3f_458_);
lean_inc(v_nsmulFn_x3f_457_);
lean_inc(v_zsmulFn_x3f_456_);
lean_inc(v_nsmulFn_455_);
lean_inc(v_zsmulFn_454_);
lean_inc(v_addFn_453_);
lean_inc(v_ltFn_x3f_452_);
lean_inc(v_leFn_x3f_451_);
lean_inc(v_one_x3f_450_);
lean_inc(v_ofNatZero_449_);
lean_inc(v_zero_448_);
lean_inc(v_charInst_x3f_447_);
lean_inc(v_fieldInst_x3f_446_);
lean_inc(v_orderedRingInst_x3f_445_);
lean_inc(v_commRingInst_x3f_444_);
lean_inc(v_ringInst_x3f_443_);
lean_inc(v_noNatDivInst_x3f_442_);
lean_inc(v_isLinearInst_x3f_441_);
lean_inc(v_orderedAddInst_x3f_440_);
lean_inc(v_isPreorderInst_x3f_439_);
lean_inc(v_lawfulOrderLTInst_x3f_438_);
lean_inc(v_ltInst_x3f_437_);
lean_inc(v_leInst_x3f_436_);
lean_inc(v_intModuleInst_435_);
lean_inc(v_u_434_);
lean_inc(v_type_433_);
lean_inc(v_ringId_x3f_432_);
lean_inc(v_id_431_);
lean_dec(v_v_430_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_487_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v_xs_x27_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_477_ = lean_box(0);
v_xs_x27_478_ = lean_array_fset(v_structs_417_, v_a_413_, v___x_477_);
v___x_479_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_414_, v_lowers_463_, v_one_415_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 32, v___x_479_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_id_431_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_ringId_x3f_432_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_type_433_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_u_434_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_intModuleInst_435_);
lean_ctor_set(v_reuseFailAlloc_486_, 5, v_leInst_x3f_436_);
lean_ctor_set(v_reuseFailAlloc_486_, 6, v_ltInst_x3f_437_);
lean_ctor_set(v_reuseFailAlloc_486_, 7, v_lawfulOrderLTInst_x3f_438_);
lean_ctor_set(v_reuseFailAlloc_486_, 8, v_isPreorderInst_x3f_439_);
lean_ctor_set(v_reuseFailAlloc_486_, 9, v_orderedAddInst_x3f_440_);
lean_ctor_set(v_reuseFailAlloc_486_, 10, v_isLinearInst_x3f_441_);
lean_ctor_set(v_reuseFailAlloc_486_, 11, v_noNatDivInst_x3f_442_);
lean_ctor_set(v_reuseFailAlloc_486_, 12, v_ringInst_x3f_443_);
lean_ctor_set(v_reuseFailAlloc_486_, 13, v_commRingInst_x3f_444_);
lean_ctor_set(v_reuseFailAlloc_486_, 14, v_orderedRingInst_x3f_445_);
lean_ctor_set(v_reuseFailAlloc_486_, 15, v_fieldInst_x3f_446_);
lean_ctor_set(v_reuseFailAlloc_486_, 16, v_charInst_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_486_, 17, v_zero_448_);
lean_ctor_set(v_reuseFailAlloc_486_, 18, v_ofNatZero_449_);
lean_ctor_set(v_reuseFailAlloc_486_, 19, v_one_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_486_, 20, v_leFn_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_486_, 21, v_ltFn_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_486_, 22, v_addFn_453_);
lean_ctor_set(v_reuseFailAlloc_486_, 23, v_zsmulFn_454_);
lean_ctor_set(v_reuseFailAlloc_486_, 24, v_nsmulFn_455_);
lean_ctor_set(v_reuseFailAlloc_486_, 25, v_zsmulFn_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_486_, 26, v_nsmulFn_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_486_, 27, v_homomulFn_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_486_, 28, v_subFn_459_);
lean_ctor_set(v_reuseFailAlloc_486_, 29, v_negFn_460_);
lean_ctor_set(v_reuseFailAlloc_486_, 30, v_vars_461_);
lean_ctor_set(v_reuseFailAlloc_486_, 31, v_varMap_462_);
lean_ctor_set(v_reuseFailAlloc_486_, 32, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_486_, 33, v_uppers_464_);
lean_ctor_set(v_reuseFailAlloc_486_, 34, v_diseqs_465_);
lean_ctor_set(v_reuseFailAlloc_486_, 35, v_assignment_466_);
lean_ctor_set(v_reuseFailAlloc_486_, 36, v_conflict_x3f_468_);
lean_ctor_set(v_reuseFailAlloc_486_, 37, v_diseqSplits_469_);
lean_ctor_set(v_reuseFailAlloc_486_, 38, v_elimEqs_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 39, v_elimStack_471_);
lean_ctor_set(v_reuseFailAlloc_486_, 40, v_occurs_472_);
lean_ctor_set(v_reuseFailAlloc_486_, 41, v_ignored_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_486_, sizeof(void*)*42, v_caseSplits_467_);
v___x_481_ = v_reuseFailAlloc_486_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_array_fset(v_xs_x27_478_, v_a_413_, v___x_481_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_482_);
v___x_484_ = v___x_428_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_typeIdOf_418_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_exprToStructId_419_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_exprToStructIdEntries_420_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_forbiddenNatModules_421_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_natStructs_422_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_natTypeIdOf_423_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_exprToNatStructId_424_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* v_a_497_, lean_object* v_p_498_, lean_object* v_one_499_, lean_object* v_s_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(v_a_497_, v_p_498_, v_one_499_, v_s_500_);
lean_dec(v_one_499_);
lean_dec(v_a_497_);
return v_res_501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_to_int(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_505_ = lean_int_neg(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* v_one_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_p_512_; lean_object* v___f_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_511_ = lean_box(0);
lean_inc(v_one_506_);
v_p_512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_512_, 0, v___x_510_);
lean_ctor_set(v_p_512_, 1, v_one_506_);
lean_ctor_set(v_p_512_, 2, v___x_511_);
lean_inc(v_a_507_);
v___f_513_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_513_, 0, v_a_507_);
lean_closure_set(v___f_513_, 1, v_p_512_);
lean_closure_set(v___f_513_, 2, v_one_506_);
v___x_514_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_515_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_514_, v___f_513_, v_a_508_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* v_one_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* v_one_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_521_, v_a_522_, v_a_523_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* v_one_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* v_p_549_, lean_object* v_x_550_, size_t v_x_551_, size_t v_x_552_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_cs_553_; size_t v_j_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_cs_553_ = lean_ctor_get(v_x_550_, 0);
v_j_554_ = lean_usize_shift_right(v_x_551_, v_x_552_);
v___x_555_ = lean_usize_to_nat(v_j_554_);
v___x_556_ = lean_array_get_size(v_cs_553_);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_dec(v___x_555_);
lean_dec(v_p_549_);
return v_x_550_;
}
else
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_575_; 
lean_inc_ref(v_cs_553_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_576_);
v___x_559_ = v_x_550_;
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
else
{
lean_dec(v_x_550_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v_i_564_; size_t v___x_565_; size_t v_shift_566_; lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_xs_x27_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_shift_left(v___x_561_, v_x_552_);
v___x_563_ = lean_usize_sub(v___x_562_, v___x_561_);
v_i_564_ = lean_usize_land(v_x_551_, v___x_563_);
v___x_565_ = ((size_t)5ULL);
v_shift_566_ = lean_usize_sub(v_x_552_, v___x_565_);
v_v_567_ = lean_array_fget(v_cs_553_, v___x_555_);
v___x_568_ = lean_box(0);
v_xs_x27_569_ = lean_array_fset(v_cs_553_, v___x_555_, v___x_568_);
v___x_570_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_549_, v_v_567_, v_i_564_, v_shift_566_);
v___x_571_ = lean_array_fset(v_xs_x27_569_, v___x_555_, v___x_570_);
lean_dec(v___x_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_571_);
v___x_573_ = v___x_559_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_vs_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_vs_577_ = lean_ctor_get(v_x_550_, 0);
v___x_578_ = lean_usize_to_nat(v_x_551_);
v___x_579_ = lean_array_get_size(v_vs_577_);
v___x_580_ = lean_nat_dec_lt(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v___x_578_);
lean_dec(v_p_549_);
return v_x_550_;
}
else
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_594_; 
lean_inc_ref(v_vs_577_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_595_);
v___x_582_ = v_x_550_;
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_x_550_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_v_584_; lean_object* v___x_585_; lean_object* v_xs_x27_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v_v_584_ = lean_array_fget(v_vs_577_, v___x_578_);
v___x_585_ = lean_box(0);
v_xs_x27_586_ = lean_array_fset(v_vs_577_, v___x_578_, v___x_585_);
v___x_587_ = lean_box(6);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_p_549_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_PersistentArray_push___redArg(v_v_584_, v___x_588_);
v___x_590_ = lean_array_fset(v_xs_x27_586_, v___x_578_, v___x_589_);
lean_dec(v___x_578_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_590_);
v___x_592_ = v___x_582_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* v_p_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
size_t v_x_258__boxed_600_; size_t v_x_259__boxed_601_; lean_object* v_res_602_; 
v_x_258__boxed_600_ = lean_unbox_usize(v_x_598_);
lean_dec(v_x_598_);
v_x_259__boxed_601_ = lean_unbox_usize(v_x_599_);
lean_dec(v_x_599_);
v_res_602_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_596_, v_x_597_, v_x_258__boxed_600_, v_x_259__boxed_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* v_p_603_, lean_object* v_t_604_, lean_object* v_i_605_){
_start:
{
lean_object* v_root_606_; lean_object* v_tail_607_; lean_object* v_size_608_; size_t v_shift_609_; lean_object* v_tailOff_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_636_; 
v_root_606_ = lean_ctor_get(v_t_604_, 0);
v_tail_607_ = lean_ctor_get(v_t_604_, 1);
v_size_608_ = lean_ctor_get(v_t_604_, 2);
v_shift_609_ = lean_ctor_get_usize(v_t_604_, 4);
v_tailOff_610_ = lean_ctor_get(v_t_604_, 3);
v_isSharedCheck_636_ = !lean_is_exclusive(v_t_604_);
if (v_isSharedCheck_636_ == 0)
{
v___x_612_ = v_t_604_;
v_isShared_613_ = v_isSharedCheck_636_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_tailOff_610_);
lean_inc(v_size_608_);
lean_inc(v_tail_607_);
lean_inc(v_root_606_);
lean_dec(v_t_604_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_636_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_le(v_tailOff_610_, v_i_605_);
if (v___x_614_ == 0)
{
size_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_615_ = lean_usize_of_nat(v_i_605_);
v___x_616_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_603_, v_root_606_, v___x_615_, v_shift_609_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_616_);
v___x_618_ = v___x_612_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_tail_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_size_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_tailOff_610_);
lean_ctor_set_usize(v_reuseFailAlloc_619_, 4, v_shift_609_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_nat_sub(v_i_605_, v_tailOff_610_);
v___x_621_ = lean_array_get_size(v_tail_607_);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_624_; 
lean_dec(v___x_620_);
lean_dec(v_p_603_);
if (v_isShared_613_ == 0)
{
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_root_606_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_tail_607_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_size_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_tailOff_610_);
lean_ctor_set_usize(v_reuseFailAlloc_625_, 4, v_shift_609_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v_v_626_; lean_object* v___x_627_; lean_object* v_xs_x27_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v_v_626_ = lean_array_fget(v_tail_607_, v___x_620_);
v___x_627_ = lean_box(0);
v_xs_x27_628_ = lean_array_fset(v_tail_607_, v___x_620_, v___x_627_);
v___x_629_ = lean_box(6);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_p_603_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_PersistentArray_push___redArg(v_v_626_, v___x_630_);
v___x_632_ = lean_array_fset(v_xs_x27_628_, v___x_620_, v___x_631_);
lean_dec(v___x_620_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_632_);
v___x_634_ = v___x_612_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_root_606_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_size_608_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_tailOff_610_);
lean_ctor_set_usize(v_reuseFailAlloc_635_, 4, v_shift_609_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* v_p_637_, lean_object* v_t_638_, lean_object* v_i_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_637_, v_t_638_, v_i_639_);
lean_dec(v_i_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* v_a_641_, lean_object* v_p_642_, lean_object* v_one_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_structs_645_; lean_object* v_typeIdOf_646_; lean_object* v_exprToStructId_647_; lean_object* v_exprToStructIdEntries_648_; lean_object* v_forbiddenNatModules_649_; lean_object* v_natStructs_650_; lean_object* v_natTypeIdOf_651_; lean_object* v_exprToNatStructId_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_structs_645_ = lean_ctor_get(v_s_644_, 0);
v_typeIdOf_646_ = lean_ctor_get(v_s_644_, 1);
v_exprToStructId_647_ = lean_ctor_get(v_s_644_, 2);
v_exprToStructIdEntries_648_ = lean_ctor_get(v_s_644_, 3);
v_forbiddenNatModules_649_ = lean_ctor_get(v_s_644_, 4);
v_natStructs_650_ = lean_ctor_get(v_s_644_, 5);
v_natTypeIdOf_651_ = lean_ctor_get(v_s_644_, 6);
v_exprToNatStructId_652_ = lean_ctor_get(v_s_644_, 7);
v___x_653_ = lean_array_get_size(v_structs_645_);
v___x_654_ = lean_nat_dec_lt(v_a_641_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v_p_642_);
return v_s_644_;
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_716_; 
lean_inc_ref(v_exprToNatStructId_652_);
lean_inc_ref(v_natTypeIdOf_651_);
lean_inc_ref(v_natStructs_650_);
lean_inc_ref(v_forbiddenNatModules_649_);
lean_inc_ref(v_exprToStructIdEntries_648_);
lean_inc_ref(v_exprToStructId_647_);
lean_inc_ref(v_typeIdOf_646_);
lean_inc_ref(v_structs_645_);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_644_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_717_ = lean_ctor_get(v_s_644_, 7);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_s_644_, 6);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_s_644_, 5);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_s_644_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_s_644_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_s_644_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_s_644_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_s_644_, 0);
lean_dec(v_unused_724_);
v___x_656_ = v_s_644_;
v_isShared_657_ = v_isSharedCheck_716_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_s_644_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_716_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_v_658_; lean_object* v_id_659_; lean_object* v_ringId_x3f_660_; lean_object* v_type_661_; lean_object* v_u_662_; lean_object* v_intModuleInst_663_; lean_object* v_leInst_x3f_664_; lean_object* v_ltInst_x3f_665_; lean_object* v_lawfulOrderLTInst_x3f_666_; lean_object* v_isPreorderInst_x3f_667_; lean_object* v_orderedAddInst_x3f_668_; lean_object* v_isLinearInst_x3f_669_; lean_object* v_noNatDivInst_x3f_670_; lean_object* v_ringInst_x3f_671_; lean_object* v_commRingInst_x3f_672_; lean_object* v_orderedRingInst_x3f_673_; lean_object* v_fieldInst_x3f_674_; lean_object* v_charInst_x3f_675_; lean_object* v_zero_676_; lean_object* v_ofNatZero_677_; lean_object* v_one_x3f_678_; lean_object* v_leFn_x3f_679_; lean_object* v_ltFn_x3f_680_; lean_object* v_addFn_681_; lean_object* v_zsmulFn_682_; lean_object* v_nsmulFn_683_; lean_object* v_zsmulFn_x3f_684_; lean_object* v_nsmulFn_x3f_685_; lean_object* v_homomulFn_x3f_686_; lean_object* v_subFn_687_; lean_object* v_negFn_688_; lean_object* v_vars_689_; lean_object* v_varMap_690_; lean_object* v_lowers_691_; lean_object* v_uppers_692_; lean_object* v_diseqs_693_; lean_object* v_assignment_694_; uint8_t v_caseSplits_695_; lean_object* v_conflict_x3f_696_; lean_object* v_diseqSplits_697_; lean_object* v_elimEqs_698_; lean_object* v_elimStack_699_; lean_object* v_occurs_700_; lean_object* v_ignored_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_715_; 
v_v_658_ = lean_array_fget(v_structs_645_, v_a_641_);
v_id_659_ = lean_ctor_get(v_v_658_, 0);
v_ringId_x3f_660_ = lean_ctor_get(v_v_658_, 1);
v_type_661_ = lean_ctor_get(v_v_658_, 2);
v_u_662_ = lean_ctor_get(v_v_658_, 3);
v_intModuleInst_663_ = lean_ctor_get(v_v_658_, 4);
v_leInst_x3f_664_ = lean_ctor_get(v_v_658_, 5);
v_ltInst_x3f_665_ = lean_ctor_get(v_v_658_, 6);
v_lawfulOrderLTInst_x3f_666_ = lean_ctor_get(v_v_658_, 7);
v_isPreorderInst_x3f_667_ = lean_ctor_get(v_v_658_, 8);
v_orderedAddInst_x3f_668_ = lean_ctor_get(v_v_658_, 9);
v_isLinearInst_x3f_669_ = lean_ctor_get(v_v_658_, 10);
v_noNatDivInst_x3f_670_ = lean_ctor_get(v_v_658_, 11);
v_ringInst_x3f_671_ = lean_ctor_get(v_v_658_, 12);
v_commRingInst_x3f_672_ = lean_ctor_get(v_v_658_, 13);
v_orderedRingInst_x3f_673_ = lean_ctor_get(v_v_658_, 14);
v_fieldInst_x3f_674_ = lean_ctor_get(v_v_658_, 15);
v_charInst_x3f_675_ = lean_ctor_get(v_v_658_, 16);
v_zero_676_ = lean_ctor_get(v_v_658_, 17);
v_ofNatZero_677_ = lean_ctor_get(v_v_658_, 18);
v_one_x3f_678_ = lean_ctor_get(v_v_658_, 19);
v_leFn_x3f_679_ = lean_ctor_get(v_v_658_, 20);
v_ltFn_x3f_680_ = lean_ctor_get(v_v_658_, 21);
v_addFn_681_ = lean_ctor_get(v_v_658_, 22);
v_zsmulFn_682_ = lean_ctor_get(v_v_658_, 23);
v_nsmulFn_683_ = lean_ctor_get(v_v_658_, 24);
v_zsmulFn_x3f_684_ = lean_ctor_get(v_v_658_, 25);
v_nsmulFn_x3f_685_ = lean_ctor_get(v_v_658_, 26);
v_homomulFn_x3f_686_ = lean_ctor_get(v_v_658_, 27);
v_subFn_687_ = lean_ctor_get(v_v_658_, 28);
v_negFn_688_ = lean_ctor_get(v_v_658_, 29);
v_vars_689_ = lean_ctor_get(v_v_658_, 30);
v_varMap_690_ = lean_ctor_get(v_v_658_, 31);
v_lowers_691_ = lean_ctor_get(v_v_658_, 32);
v_uppers_692_ = lean_ctor_get(v_v_658_, 33);
v_diseqs_693_ = lean_ctor_get(v_v_658_, 34);
v_assignment_694_ = lean_ctor_get(v_v_658_, 35);
v_caseSplits_695_ = lean_ctor_get_uint8(v_v_658_, sizeof(void*)*42);
v_conflict_x3f_696_ = lean_ctor_get(v_v_658_, 36);
v_diseqSplits_697_ = lean_ctor_get(v_v_658_, 37);
v_elimEqs_698_ = lean_ctor_get(v_v_658_, 38);
v_elimStack_699_ = lean_ctor_get(v_v_658_, 39);
v_occurs_700_ = lean_ctor_get(v_v_658_, 40);
v_ignored_701_ = lean_ctor_get(v_v_658_, 41);
v_isSharedCheck_715_ = !lean_is_exclusive(v_v_658_);
if (v_isSharedCheck_715_ == 0)
{
v___x_703_ = v_v_658_;
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_ignored_701_);
lean_inc(v_occurs_700_);
lean_inc(v_elimStack_699_);
lean_inc(v_elimEqs_698_);
lean_inc(v_diseqSplits_697_);
lean_inc(v_conflict_x3f_696_);
lean_inc(v_assignment_694_);
lean_inc(v_diseqs_693_);
lean_inc(v_uppers_692_);
lean_inc(v_lowers_691_);
lean_inc(v_varMap_690_);
lean_inc(v_vars_689_);
lean_inc(v_negFn_688_);
lean_inc(v_subFn_687_);
lean_inc(v_homomulFn_x3f_686_);
lean_inc(v_nsmulFn_x3f_685_);
lean_inc(v_zsmulFn_x3f_684_);
lean_inc(v_nsmulFn_683_);
lean_inc(v_zsmulFn_682_);
lean_inc(v_addFn_681_);
lean_inc(v_ltFn_x3f_680_);
lean_inc(v_leFn_x3f_679_);
lean_inc(v_one_x3f_678_);
lean_inc(v_ofNatZero_677_);
lean_inc(v_zero_676_);
lean_inc(v_charInst_x3f_675_);
lean_inc(v_fieldInst_x3f_674_);
lean_inc(v_orderedRingInst_x3f_673_);
lean_inc(v_commRingInst_x3f_672_);
lean_inc(v_ringInst_x3f_671_);
lean_inc(v_noNatDivInst_x3f_670_);
lean_inc(v_isLinearInst_x3f_669_);
lean_inc(v_orderedAddInst_x3f_668_);
lean_inc(v_isPreorderInst_x3f_667_);
lean_inc(v_lawfulOrderLTInst_x3f_666_);
lean_inc(v_ltInst_x3f_665_);
lean_inc(v_leInst_x3f_664_);
lean_inc(v_intModuleInst_663_);
lean_inc(v_u_662_);
lean_inc(v_type_661_);
lean_inc(v_ringId_x3f_660_);
lean_inc(v_id_659_);
lean_dec(v_v_658_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_715_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v_xs_x27_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = lean_box(0);
v_xs_x27_706_ = lean_array_fset(v_structs_645_, v_a_641_, v___x_705_);
v___x_707_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_642_, v_diseqs_693_, v_one_643_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 34, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_id_659_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_ringId_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_type_661_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_u_662_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_intModuleInst_663_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v_leInst_x3f_664_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v_ltInst_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_lawfulOrderLTInst_x3f_666_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v_isPreorderInst_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_orderedAddInst_x3f_668_);
lean_ctor_set(v_reuseFailAlloc_714_, 10, v_isLinearInst_x3f_669_);
lean_ctor_set(v_reuseFailAlloc_714_, 11, v_noNatDivInst_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_714_, 12, v_ringInst_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_714_, 13, v_commRingInst_x3f_672_);
lean_ctor_set(v_reuseFailAlloc_714_, 14, v_orderedRingInst_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_714_, 15, v_fieldInst_x3f_674_);
lean_ctor_set(v_reuseFailAlloc_714_, 16, v_charInst_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_714_, 17, v_zero_676_);
lean_ctor_set(v_reuseFailAlloc_714_, 18, v_ofNatZero_677_);
lean_ctor_set(v_reuseFailAlloc_714_, 19, v_one_x3f_678_);
lean_ctor_set(v_reuseFailAlloc_714_, 20, v_leFn_x3f_679_);
lean_ctor_set(v_reuseFailAlloc_714_, 21, v_ltFn_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_714_, 22, v_addFn_681_);
lean_ctor_set(v_reuseFailAlloc_714_, 23, v_zsmulFn_682_);
lean_ctor_set(v_reuseFailAlloc_714_, 24, v_nsmulFn_683_);
lean_ctor_set(v_reuseFailAlloc_714_, 25, v_zsmulFn_x3f_684_);
lean_ctor_set(v_reuseFailAlloc_714_, 26, v_nsmulFn_x3f_685_);
lean_ctor_set(v_reuseFailAlloc_714_, 27, v_homomulFn_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_714_, 28, v_subFn_687_);
lean_ctor_set(v_reuseFailAlloc_714_, 29, v_negFn_688_);
lean_ctor_set(v_reuseFailAlloc_714_, 30, v_vars_689_);
lean_ctor_set(v_reuseFailAlloc_714_, 31, v_varMap_690_);
lean_ctor_set(v_reuseFailAlloc_714_, 32, v_lowers_691_);
lean_ctor_set(v_reuseFailAlloc_714_, 33, v_uppers_692_);
lean_ctor_set(v_reuseFailAlloc_714_, 34, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 35, v_assignment_694_);
lean_ctor_set(v_reuseFailAlloc_714_, 36, v_conflict_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_714_, 37, v_diseqSplits_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 38, v_elimEqs_698_);
lean_ctor_set(v_reuseFailAlloc_714_, 39, v_elimStack_699_);
lean_ctor_set(v_reuseFailAlloc_714_, 40, v_occurs_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 41, v_ignored_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*42, v_caseSplits_695_);
v___x_709_ = v_reuseFailAlloc_714_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_array_fset(v_xs_x27_706_, v_a_641_, v___x_709_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_710_);
v___x_712_ = v___x_656_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_typeIdOf_646_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_exprToStructId_647_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_exprToStructIdEntries_648_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_forbiddenNatModules_649_);
lean_ctor_set(v_reuseFailAlloc_713_, 5, v_natStructs_650_);
lean_ctor_set(v_reuseFailAlloc_713_, 6, v_natTypeIdOf_651_);
lean_ctor_set(v_reuseFailAlloc_713_, 7, v_exprToNatStructId_652_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* v_a_725_, lean_object* v_p_726_, lean_object* v_one_727_, lean_object* v_s_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(v_a_725_, v_p_726_, v_one_727_, v_s_728_);
lean_dec(v_one_727_);
lean_dec(v_a_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* v_one_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_p_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_735_ = lean_box(0);
lean_inc(v_one_730_);
v_p_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_736_, 0, v___x_734_);
lean_ctor_set(v_p_736_, 1, v_one_730_);
lean_ctor_set(v_p_736_, 2, v___x_735_);
lean_inc(v_a_731_);
v___f_737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_737_, 0, v_a_731_);
lean_closure_set(v___f_737_, 1, v_p_736_);
lean_closure_set(v___f_737_, 2, v_one_730_);
v___x_738_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_739_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_738_, v___f_737_, v_a_732_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* v_one_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* v_one_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_745_, v_a_746_, v_a_747_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* v_one_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec(v_a_761_);
lean_dec(v_a_760_);
return v_res_772_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* v_isCharInst_x3f_773_){
_start:
{
if (lean_obj_tag(v_isCharInst_x3f_773_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v_snd_776_; lean_object* v___x_777_; uint8_t v___x_778_; uint8_t v___x_779_; 
v_val_775_ = lean_ctor_get(v_isCharInst_x3f_773_, 0);
v_snd_776_ = lean_ctor_get(v_val_775_, 1);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_dec_eq(v_snd_776_, v___x_777_);
v___x_779_ = lean_bool_not(v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_780_);
lean_dec(v_isCharInst_x3f_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_786_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; uint8_t v_lia_801_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v_lia_801_ = lean_ctor_get_uint8(v_a_800_, sizeof(void*)*13 + 23);
lean_dec(v_a_800_);
if (v_lia_801_ == 0)
{
lean_dec_ref(v_type_783_);
goto v___jp_795_;
}
else
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; uint8_t v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
v___x_804_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_804_ == 0)
{
lean_dec_ref_known(v___x_802_, 1);
goto v___jp_795_;
}
else
{
return v___x_802_;
}
}
else
{
return v___x_802_;
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_type_783_);
v_a_805_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_799_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
v___jp_795_:
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = 0;
v___x_797_ = lean_box(v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec(v_a_814_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_826_) == 1)
{
lean_object* v_val_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_865_; 
v_val_838_ = lean_ctor_get(v_ringId_x3f_826_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_ringId_x3f_826_);
if (v_isSharedCheck_865_ == 0)
{
v___x_840_ = v_ringId_x3f_826_;
v_isShared_841_ = v_isSharedCheck_865_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_val_838_);
lean_dec(v_ringId_x3f_826_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_865_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = 0;
v___x_843_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_843_, 0, v_val_838_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*1, v___x_842_);
v___x_844_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_843_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_856_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_commRingInst_849_; lean_object* v___x_851_; 
v_commRingInst_849_ = lean_ctor_get(v_a_845_, 4);
lean_inc_ref(v_commRingInst_849_);
lean_dec(v_a_845_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_commRingInst_849_);
v___x_851_ = v___x_840_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_commRingInst_849_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_del_object(v___x_840_);
v_a_857_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_844_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_844_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_ringId_x3f_826_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_895_, lean_object* v_type_896_, lean_object* v_commRingInst_x3f_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_897_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_917_; 
v_val_904_ = lean_ctor_get(v_commRingInst_x3f_897_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_commRingInst_x3f_897_);
if (v_isSharedCheck_917_ == 0)
{
v___x_906_ = v_commRingInst_x3f_897_;
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v_commRingInst_x3f_897_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v_u_895_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_mkConst(v___x_908_, v___x_910_);
v___x_912_ = l_Lean_mkAppB(v___x_911_, v_type_896_, v_val_904_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_912_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_commRingInst_x3f_897_);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v_u_895_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_mkConst(v___x_918_, v___x_920_);
v___x_922_ = l_Lean_Expr_app___override(v___x_921_, v_type_896_);
v___x_923_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_922_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_924_, lean_object* v_type_925_, lean_object* v_commRingInst_x3f_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_924_, v_type_925_, v_commRingInst_x3f_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_934_, lean_object* v_type_935_, lean_object* v_commRingInst_x3f_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_934_, v_type_935_, v_commRingInst_x3f_936_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_949_, lean_object* v_type_950_, lean_object* v_commRingInst_x3f_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_949_, v_type_950_, v_commRingInst_x3f_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_975_, lean_object* v_type_976_, lean_object* v_ringInst_x3f_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_977_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_997_; 
v_val_984_ = lean_ctor_get(v_ringInst_x3f_977_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_ringInst_x3f_977_);
if (v_isSharedCheck_997_ == 0)
{
v___x_986_ = v_ringInst_x3f_977_;
v_isShared_987_ = v_isSharedCheck_997_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v_ringInst_x3f_977_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_997_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_990_, 0, v_u_975_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_mkConst(v___x_988_, v___x_990_);
v___x_992_ = l_Lean_mkAppB(v___x_991_, v_type_976_, v_val_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_992_);
v___x_994_ = v___x_986_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_ringInst_x3f_977_);
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_u_975_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_mkConst(v___x_998_, v___x_1000_);
v___x_1002_ = l_Lean_Expr_app___override(v___x_1001_, v_type_976_);
v___x_1003_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1002_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1004_, lean_object* v_type_1005_, lean_object* v_ringInst_x3f_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1004_, v_type_1005_, v_ringInst_x3f_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1014_, lean_object* v_type_1015_, lean_object* v_ringInst_x3f_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1014_, v_type_1015_, v_ringInst_x3f_1016_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1029_, lean_object* v_type_1030_, lean_object* v_ringInst_x3f_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1029_, v_type_1030_, v_ringInst_x3f_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1055_, lean_object* v_type_1056_, lean_object* v_ringInst_x3f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1057_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1077_; 
v_val_1064_ = lean_ctor_get(v_ringInst_x3f_1057_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_ringInst_x3f_1057_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1066_ = v_ringInst_x3f_1057_;
v_isShared_1067_ = v_isSharedCheck_1077_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v_ringInst_x3f_1057_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1077_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_u_1055_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_mkConst(v___x_1068_, v___x_1070_);
v___x_1072_ = l_Lean_mkAppB(v___x_1071_, v_type_1056_, v_val_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1072_);
v___x_1074_ = v___x_1066_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_ringInst_x3f_1057_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_u_1055_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_mkConst(v___x_1078_, v___x_1080_);
v___x_1082_ = l_Lean_Expr_app___override(v___x_1081_, v_type_1056_);
v___x_1083_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1082_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1084_, lean_object* v_type_1085_, lean_object* v_ringInst_x3f_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1084_, v_type_1085_, v_ringInst_x3f_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1094_, lean_object* v_type_1095_, lean_object* v_ringInst_x3f_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1094_, v_type_1095_, v_ringInst_x3f_1096_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1109_, lean_object* v_type_1110_, lean_object* v_ringInst_x3f_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1109_, v_type_1110_, v_ringInst_x3f_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec(v_a_1112_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1131_, lean_object* v_type_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_u_1131_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
lean_inc_ref(v___x_1146_);
v___x_1147_ = l_Lean_mkConst(v___x_1144_, v___x_1146_);
lean_inc_ref(v_type_1132_);
v___x_1148_ = l_Lean_Expr_app___override(v___x_1147_, v_type_1132_);
v___x_1149_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1148_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1231_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1231_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1231_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
if (lean_obj_tag(v_a_1150_) == 1)
{
lean_object* v_val_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1152_);
v_val_1154_ = lean_ctor_get(v_a_1150_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_a_1150_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1156_ = v_a_1150_;
v_isShared_1157_ = v_isSharedCheck_1226_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_val_1154_);
lean_dec(v_a_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1226_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1159_ = l_Lean_mkConst(v___x_1158_, v___x_1146_);
lean_inc_ref(v_type_1132_);
v___x_1160_ = l_Lean_mkAppB(v___x_1159_, v_type_1132_, v_val_1154_);
v___x_1161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1160_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1217_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = l_Lean_Meta_mkNumeral(v_type_1132_, v___x_1173_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc_n(v_a_1175_, 2);
lean_dec_ref_known(v___x_1174_, 1);
lean_inc(v_a_1162_);
v___x_1176_ = l_Lean_Meta_isDefEqD(v_a_1162_, v_a_1175_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_unbox(v_a_1177_);
lean_dec(v_a_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v_a_1180_; lean_object* v___x_1181_; 
lean_inc(v_a_1162_);
v___x_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1162_, v_a_1175_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___x_1181_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1137_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; uint8_t v_verbose_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v_verbose_1183_ = lean_ctor_get_uint8(v_a_1182_, 0);
lean_dec(v_a_1182_);
if (v_verbose_1183_ == 0)
{
lean_dec(v_a_1180_);
goto v___jp_1166_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_Sym_reportIssue(v_a_1180_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref_known(v___x_1184_, 1);
goto v___jp_1166_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_del_object(v___x_1164_);
lean_dec(v_a_1162_);
lean_del_object(v___x_1156_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1180_);
lean_del_object(v___x_1164_);
lean_dec(v_a_1162_);
lean_del_object(v___x_1156_);
v_a_1193_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1181_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1181_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_dec(v_a_1175_);
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_a_1175_);
lean_del_object(v___x_1164_);
lean_dec(v_a_1162_);
lean_del_object(v___x_1156_);
v_a_1201_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1176_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1176_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
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
lean_del_object(v___x_1164_);
lean_dec(v_a_1162_);
lean_del_object(v___x_1156_);
v_a_1209_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1174_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1174_);
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
v___jp_1166_:
{
lean_object* v___x_1168_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_a_1162_);
v___x_1168_ = v___x_1156_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1162_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
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
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1156_);
lean_dec_ref(v_type_1132_);
v_a_1218_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1161_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1161_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec(v_a_1150_);
lean_dec_ref_known(v___x_1146_, 2);
lean_dec_ref(v_type_1132_);
v___x_1227_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1227_);
v___x_1229_ = v___x_1152_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1146_, 2);
lean_dec_ref(v_type_1132_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1232_, lean_object* v_type_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1232_, v_type_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
return v_res_1245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1254_, lean_object* v_type_1255_, lean_object* v_semiringInst_x3f_1256_, lean_object* v_leInst_x3f_1257_, lean_object* v_ltInst_x3f_1258_, lean_object* v_preorderInst_x3f_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1256_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1257_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1258_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1259_) == 1)
{
lean_object* v_val_1270_; lean_object* v_val_1271_; lean_object* v_val_1272_; lean_object* v_val_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_isOrdType_1278_; lean_object* v___x_1279_; 
v_val_1270_ = lean_ctor_get(v_semiringInst_x3f_1256_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_semiringInst_x3f_1256_, 1);
v_val_1271_ = lean_ctor_get(v_leInst_x3f_1257_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_leInst_x3f_1257_, 1);
v_val_1272_ = lean_ctor_get(v_ltInst_x3f_1258_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v_ltInst_x3f_1258_, 1);
v_val_1273_ = lean_ctor_get(v_preorderInst_x3f_1259_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v_preorderInst_x3f_1259_, 1);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_u_1254_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_mkConst(v___x_1274_, v___x_1276_);
v_isOrdType_1278_ = l_Lean_mkApp5(v___x_1277_, v_type_1255_, v_val_1270_, v_val_1271_, v_val_1272_, v_val_1273_);
lean_inc_ref(v_isOrdType_1278_);
v___x_1279_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1278_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
if (lean_obj_tag(v_a_1280_) == 1)
{
lean_dec_ref_known(v_a_1280_, 1);
lean_dec_ref(v_isOrdType_1278_);
return v___x_1279_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1260_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; uint8_t v_verbose_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v_verbose_1283_ = lean_ctor_get_uint8(v_a_1282_, 0);
lean_dec(v_a_1282_);
if (v_verbose_1283_ == 0)
{
lean_dec_ref(v_isOrdType_1278_);
goto v___jp_1267_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1285_ = l_Lean_indentExpr(v_isOrdType_1278_);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_Meta_Sym_reportIssue(v___x_1286_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref_known(v___x_1287_, 1);
goto v___jp_1267_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_isOrdType_1278_);
v_a_1296_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1281_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1281_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1278_);
return v___x_1279_;
}
}
else
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref_known(v_leInst_x3f_1257_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1256_, 1);
lean_dec(v_preorderInst_x3f_1259_);
lean_dec_ref(v_type_1255_);
lean_dec(v_u_1254_);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_ltInst_x3f_1258_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_ltInst_x3f_1258_, 0);
lean_dec(v_unused_1312_);
v___x_1305_ = v_ltInst_x3f_1258_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_ltInst_x3f_1258_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref_known(v_semiringInst_x3f_1256_, 1);
lean_dec(v_preorderInst_x3f_1259_);
lean_dec(v_ltInst_x3f_1258_);
lean_dec_ref(v_type_1255_);
lean_dec(v_u_1254_);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_leInst_x3f_1257_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_leInst_x3f_1257_, 0);
lean_dec(v_unused_1321_);
v___x_1314_ = v_leInst_x3f_1257_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_leInst_x3f_1257_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_box(0);
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
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
else
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_preorderInst_x3f_1259_);
lean_dec(v_ltInst_x3f_1258_);
lean_dec(v_leInst_x3f_1257_);
lean_dec_ref(v_type_1255_);
lean_dec(v_u_1254_);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_semiringInst_x3f_1256_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_semiringInst_x3f_1256_, 0);
lean_dec(v_unused_1330_);
v___x_1323_ = v_semiringInst_x3f_1256_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_semiringInst_x3f_1256_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v_preorderInst_x3f_1259_);
lean_dec(v_ltInst_x3f_1258_);
lean_dec(v_leInst_x3f_1257_);
lean_dec(v_semiringInst_x3f_1256_);
lean_dec_ref(v_type_1255_);
lean_dec(v_u_1254_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
v___jp_1267_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1333_, lean_object* v_type_1334_, lean_object* v_semiringInst_x3f_1335_, lean_object* v_leInst_x3f_1336_, lean_object* v_ltInst_x3f_1337_, lean_object* v_preorderInst_x3f_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1333_, v_type_1334_, v_semiringInst_x3f_1335_, v_leInst_x3f_1336_, v_ltInst_x3f_1337_, v_preorderInst_x3f_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1347_, lean_object* v_type_1348_, lean_object* v_semiringInst_x3f_1349_, lean_object* v_leInst_x3f_1350_, lean_object* v_ltInst_x3f_1351_, lean_object* v_preorderInst_x3f_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1347_, v_type_1348_, v_semiringInst_x3f_1349_, v_leInst_x3f_1350_, v_ltInst_x3f_1351_, v_preorderInst_x3f_1352_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1365_ = _args[0];
lean_object* v_type_1366_ = _args[1];
lean_object* v_semiringInst_x3f_1367_ = _args[2];
lean_object* v_leInst_x3f_1368_ = _args[3];
lean_object* v_ltInst_x3f_1369_ = _args[4];
lean_object* v_preorderInst_x3f_1370_ = _args[5];
lean_object* v_a_1371_ = _args[6];
lean_object* v_a_1372_ = _args[7];
lean_object* v_a_1373_ = _args[8];
lean_object* v_a_1374_ = _args[9];
lean_object* v_a_1375_ = _args[10];
lean_object* v_a_1376_ = _args[11];
lean_object* v_a_1377_ = _args[12];
lean_object* v_a_1378_ = _args[13];
lean_object* v_a_1379_ = _args[14];
lean_object* v_a_1380_ = _args[15];
lean_object* v_a_1381_ = _args[16];
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1365_, v_type_1366_, v_semiringInst_x3f_1367_, v_leInst_x3f_1368_, v_ltInst_x3f_1369_, v_preorderInst_x3f_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
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
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1393_, lean_object* v_type_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_natModuleType_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_u_1393_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
lean_inc_ref(v___x_1403_);
v___x_1404_ = l_Lean_mkConst(v___x_1401_, v___x_1403_);
lean_inc_ref(v_type_1394_);
v_natModuleType_1405_ = l_Lean_Expr_app___override(v___x_1404_, v_type_1394_);
v___x_1406_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1405_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1420_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
if (lean_obj_tag(v_a_1407_) == 1)
{
lean_object* v_val_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_del_object(v___x_1409_);
v_val_1411_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_a_1407_, 1);
v___x_1412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1413_ = l_Lean_mkConst(v___x_1412_, v___x_1403_);
v___x_1414_ = l_Lean_mkAppB(v___x_1413_, v_type_1394_, v_val_1411_);
v___x_1415_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1414_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec(v_a_1407_);
lean_dec_ref_known(v___x_1403_, 2);
lean_dec_ref(v_type_1394_);
v___x_1416_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1416_);
v___x_1418_ = v___x_1409_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1403_, 2);
lean_dec_ref(v_type_1394_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1421_, lean_object* v_type_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1421_, v_type_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1430_, lean_object* v_type_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1430_, v_type_1431_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1444_, lean_object* v_type_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1444_, v_type_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec(v_a_1446_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1458_, lean_object* v_u_1459_, lean_object* v_type_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_u_1459_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_mkConst(v_declName_1458_, v___x_1468_);
v___x_1470_ = l_Lean_Expr_app___override(v___x_1469_, v_type_1460_);
v___x_1471_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1470_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1472_, lean_object* v_u_1473_, lean_object* v_type_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1472_, v_u_1473_, v_type_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1482_, lean_object* v_u_1483_, lean_object* v_type_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1482_, v_u_1483_, v_type_1484_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1497_, lean_object* v_u_1498_, lean_object* v_type_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1497_, v_u_1498_, v_type_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec(v_a_1500_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1512_, lean_object* v_u_1513_, lean_object* v_type_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1523_, 0, v_u_1513_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_mkConst(v_declName_1512_, v___x_1523_);
v___x_1525_ = l_Lean_Expr_app___override(v___x_1524_, v_type_1514_);
v___x_1526_ = l_Lean_Meta_Sym_synthInstance(v___x_1525_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1527_, lean_object* v_u_1528_, lean_object* v_type_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1527_, v_u_1528_, v_type_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1538_, lean_object* v_u_1539_, lean_object* v_type_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1538_, v_u_1539_, v_type_1540_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1553_, lean_object* v_u_1554_, lean_object* v_type_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1553_, v_u_1554_, v_type_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec(v_a_1556_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1568_, lean_object* v_u_1569_, lean_object* v_type_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1578_ = lean_box(0);
lean_inc_n(v_u_1569_, 2);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_u_1569_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_u_1569_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_u_1569_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_mkConst(v_declName_1568_, v___x_1581_);
lean_inc_ref_n(v_type_1570_, 2);
v___x_1583_ = l_Lean_mkApp3(v___x_1582_, v_type_1570_, v_type_1570_, v_type_1570_);
v___x_1584_ = l_Lean_Meta_Sym_synthInstance(v___x_1583_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1585_, lean_object* v_u_1586_, lean_object* v_type_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1585_, v_u_1586_, v_type_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1596_, lean_object* v_u_1597_, lean_object* v_type_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1596_, v_u_1597_, v_type_1598_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1611_, lean_object* v_u_1612_, lean_object* v_type_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1611_, v_u_1612_, v_type_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec(v_a_1614_);
return v_res_1625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = l_Lean_Level_ofNat(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1631_, lean_object* v_type_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1641_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1642_ = lean_box(0);
lean_inc(v_u_1631_);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_u_1631_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_u_1631_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1641_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_mkConst(v___x_1640_, v___x_1645_);
v___x_1647_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1632_);
v___x_1648_ = l_Lean_mkApp3(v___x_1646_, v___x_1647_, v_type_1632_, v_type_1632_);
v___x_1649_ = l_Lean_Meta_Sym_synthInstance(v___x_1648_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1650_, lean_object* v_type_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1650_, v_type_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1660_, lean_object* v_type_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1660_, v_type_1661_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1674_, lean_object* v_type_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1674_, v_type_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec(v_a_1676_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1688_, lean_object* v_type_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1699_ = lean_box(0);
lean_inc(v_u_1688_);
v___x_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_u_1688_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_u_1688_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1698_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_mkConst(v___x_1697_, v___x_1702_);
v___x_1704_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1689_);
v___x_1705_ = l_Lean_mkApp3(v___x_1703_, v___x_1704_, v_type_1689_, v_type_1689_);
v___x_1706_ = l_Lean_Meta_Sym_synthInstance(v___x_1705_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1707_, lean_object* v_type_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1707_, v_type_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1717_, lean_object* v_type_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1717_, v_type_1718_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1731_, lean_object* v_type_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1731_, v_type_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec(v_a_1733_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1745_, lean_object* v_parentInst_x3f_1746_, lean_object* v_childInst_x3f_1747_, lean_object* v_toFieldName_1748_, lean_object* v_u_1749_, lean_object* v_type_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1745_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1746_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1747_) == 1)
{
lean_object* v_val_1761_; lean_object* v_val_1762_; lean_object* v_val_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_toField_1767_; lean_object* v___x_1768_; 
v_val_1761_ = lean_ctor_get(v_leInst_x3f_1745_, 0);
lean_inc(v_val_1761_);
lean_dec_ref_known(v_leInst_x3f_1745_, 1);
v_val_1762_ = lean_ctor_get(v_parentInst_x3f_1746_, 0);
lean_inc_n(v_val_1762_, 2);
lean_dec_ref_known(v_parentInst_x3f_1746_, 1);
v_val_1763_ = lean_ctor_get(v_childInst_x3f_1747_, 0);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_u_1749_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_mkConst(v_toFieldName_1748_, v___x_1765_);
lean_inc(v_val_1763_);
v_toField_1767_ = l_Lean_mkApp3(v___x_1766_, v_type_1750_, v_val_1761_, v_val_1763_);
lean_inc_ref(v_toField_1767_);
v___x_1768_ = l_Lean_Meta_isDefEqD(v_val_1762_, v_toField_1767_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1799_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_unbox(v_a_1769_);
lean_dec(v_a_1769_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1776_; 
lean_del_object(v___x_1771_);
lean_dec_ref_known(v_childInst_x3f_1747_, 1);
v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1762_, v_toField_1767_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1751_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; uint8_t v_verbose_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v_verbose_1778_ = lean_ctor_get_uint8(v_a_1777_, 0);
lean_dec(v_a_1777_);
if (v_verbose_1778_ == 0)
{
lean_dec(v_a_1775_);
goto v___jp_1758_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Sym_reportIssue(v_a_1775_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_dec_ref_known(v___x_1779_, 1);
goto v___jp_1758_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_a_1775_);
v_a_1788_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1776_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1776_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v___x_1797_; 
lean_dec_ref(v_toField_1767_);
lean_dec(v_val_1762_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v_childInst_x3f_1747_);
v___x_1797_ = v___x_1771_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_childInst_x3f_1747_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_toField_1767_);
lean_dec(v_val_1762_);
lean_dec_ref_known(v_childInst_x3f_1747_, 1);
v_a_1800_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1768_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1768_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref_known(v_leInst_x3f_1745_, 1);
lean_dec_ref(v_type_1750_);
lean_dec(v_u_1749_);
lean_dec(v_toFieldName_1748_);
lean_dec(v_childInst_x3f_1747_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_parentInst_x3f_1746_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_parentInst_x3f_1746_, 0);
lean_dec(v_unused_1816_);
v___x_1809_ = v_parentInst_x3f_1746_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_parentInst_x3f_1746_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_type_1750_);
lean_dec(v_u_1749_);
lean_dec(v_toFieldName_1748_);
lean_dec(v_childInst_x3f_1747_);
lean_dec(v_parentInst_x3f_1746_);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_leInst_x3f_1745_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v_leInst_x3f_1745_, 0);
lean_dec(v_unused_1825_);
v___x_1818_ = v_leInst_x3f_1745_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v_leInst_x3f_1745_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_type_1750_);
lean_dec(v_u_1749_);
lean_dec(v_toFieldName_1748_);
lean_dec(v_childInst_x3f_1747_);
lean_dec(v_parentInst_x3f_1746_);
lean_dec(v_leInst_x3f_1745_);
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
v___jp_1758_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1828_, lean_object* v_parentInst_x3f_1829_, lean_object* v_childInst_x3f_1830_, lean_object* v_toFieldName_1831_, lean_object* v_u_1832_, lean_object* v_type_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1828_, v_parentInst_x3f_1829_, v_childInst_x3f_1830_, v_toFieldName_1831_, v_u_1832_, v_type_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1842_, lean_object* v_parentInst_x3f_1843_, lean_object* v_childInst_x3f_1844_, lean_object* v_toFieldName_1845_, lean_object* v_u_1846_, lean_object* v_type_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1842_, v_parentInst_x3f_1843_, v_childInst_x3f_1844_, v_toFieldName_1845_, v_u_1846_, v_type_1847_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1860_ = _args[0];
lean_object* v_parentInst_x3f_1861_ = _args[1];
lean_object* v_childInst_x3f_1862_ = _args[2];
lean_object* v_toFieldName_1863_ = _args[3];
lean_object* v_u_1864_ = _args[4];
lean_object* v_type_1865_ = _args[5];
lean_object* v_a_1866_ = _args[6];
lean_object* v_a_1867_ = _args[7];
lean_object* v_a_1868_ = _args[8];
lean_object* v_a_1869_ = _args[9];
lean_object* v_a_1870_ = _args[10];
lean_object* v_a_1871_ = _args[11];
lean_object* v_a_1872_ = _args[12];
lean_object* v_a_1873_ = _args[13];
lean_object* v_a_1874_ = _args[14];
lean_object* v_a_1875_ = _args[15];
lean_object* v_a_1876_ = _args[16];
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1860_, v_parentInst_x3f_1861_, v_childInst_x3f_1862_, v_toFieldName_1863_, v_u_1864_, v_type_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1878_, lean_object* v_inst_1879_, lean_object* v_toFieldName_1880_, lean_object* v_u_1881_, lean_object* v_type_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_toField_1891_; lean_object* v___x_1892_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_u_1881_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = l_Lean_mkConst(v_toFieldName_1880_, v___x_1889_);
v_toField_1891_ = l_Lean_mkAppB(v___x_1890_, v_type_1882_, v_inst_1879_);
v___x_1892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1878_, v_toField_1891_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1893_, lean_object* v_inst_1894_, lean_object* v_toFieldName_1895_, lean_object* v_u_1896_, lean_object* v_type_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1893_, v_inst_1894_, v_toFieldName_1895_, v_u_1896_, v_type_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1904_, lean_object* v_inst_1905_, lean_object* v_toFieldName_1906_, lean_object* v_u_1907_, lean_object* v_type_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1904_, v_inst_1905_, v_toFieldName_1906_, v_u_1907_, v_type_1908_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1921_, lean_object* v_inst_1922_, lean_object* v_toFieldName_1923_, lean_object* v_u_1924_, lean_object* v_type_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1921_, v_inst_1922_, v_toFieldName_1923_, v_u_1924_, v_type_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec(v_a_1926_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1938_, lean_object* v_inst_1939_, lean_object* v_toFieldName_1940_, lean_object* v_toHeteroName_1941_, lean_object* v_u_1942_, lean_object* v_type_1943_, lean_object* v_extraType_x3f_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_toField_1953_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_u_1942_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
lean_inc_ref(v___x_1951_);
v___x_1952_ = l_Lean_mkConst(v_toFieldName_1940_, v___x_1951_);
lean_inc_ref(v_type_1943_);
v_toField_1953_ = l_Lean_mkAppB(v___x_1952_, v_type_1943_, v_inst_1939_);
if (lean_obj_tag(v_extraType_x3f_1944_) == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = l_Lean_mkConst(v_toHeteroName_1941_, v___x_1951_);
v___x_1955_ = l_Lean_mkAppB(v___x_1954_, v_type_1943_, v_toField_1953_);
v___x_1956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1938_, v___x_1955_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1956_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_val_1957_ = lean_ctor_get(v_extraType_x3f_1944_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v_extraType_x3f_1944_, 1);
v___x_1958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___x_1951_);
v___x_1960_ = l_Lean_mkConst(v_toHeteroName_1941_, v___x_1959_);
v___x_1961_ = l_Lean_mkApp3(v___x_1960_, v_val_1957_, v_type_1943_, v_toField_1953_);
v___x_1962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1938_, v___x_1961_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1963_, lean_object* v_inst_1964_, lean_object* v_toFieldName_1965_, lean_object* v_toHeteroName_1966_, lean_object* v_u_1967_, lean_object* v_type_1968_, lean_object* v_extraType_x3f_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1963_, v_inst_1964_, v_toFieldName_1965_, v_toHeteroName_1966_, v_u_1967_, v_type_1968_, v_extraType_x3f_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1976_, lean_object* v_inst_1977_, lean_object* v_toFieldName_1978_, lean_object* v_toHeteroName_1979_, lean_object* v_u_1980_, lean_object* v_type_1981_, lean_object* v_extraType_x3f_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1976_, v_inst_1977_, v_toFieldName_1978_, v_toHeteroName_1979_, v_u_1980_, v_type_1981_, v_extraType_x3f_1982_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_1995_ = _args[0];
lean_object* v_inst_1996_ = _args[1];
lean_object* v_toFieldName_1997_ = _args[2];
lean_object* v_toHeteroName_1998_ = _args[3];
lean_object* v_u_1999_ = _args[4];
lean_object* v_type_2000_ = _args[5];
lean_object* v_extraType_x3f_2001_ = _args[6];
lean_object* v_a_2002_ = _args[7];
lean_object* v_a_2003_ = _args[8];
lean_object* v_a_2004_ = _args[9];
lean_object* v_a_2005_ = _args[10];
lean_object* v_a_2006_ = _args[11];
lean_object* v_a_2007_ = _args[12];
lean_object* v_a_2008_ = _args[13];
lean_object* v_a_2009_ = _args[14];
lean_object* v_a_2010_ = _args[15];
lean_object* v_a_2011_ = _args[16];
lean_object* v_a_2012_ = _args[17];
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_1995_, v_inst_1996_, v_toFieldName_1997_, v_toHeteroName_1998_, v_u_1999_, v_type_2000_, v_extraType_x3f_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec(v_a_2002_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2018_, lean_object* v_type_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_smulType_2035_; lean_object* v___x_2036_; 
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2029_ = lean_box(0);
lean_inc(v_u_2018_);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_u_2018_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_u_2018_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2028_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_inc_ref(v___x_2032_);
v___x_2033_ = l_Lean_mkConst(v___x_2027_, v___x_2032_);
v___x_2034_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2019_, 2);
v_smulType_2035_ = l_Lean_mkApp3(v___x_2033_, v___x_2034_, v_type_2019_, v_type_2019_);
v___x_2036_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2035_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2073_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2073_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2073_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2039_);
v_val_2041_ = lean_ctor_get(v_a_2037_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2043_ = v_a_2037_;
v_isShared_2044_ = v_isSharedCheck_2068_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v_a_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2068_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2046_ = l_Lean_mkConst(v___x_2045_, v___x_2032_);
lean_inc_ref(v_type_2019_);
v___x_2047_ = l_Lean_mkApp4(v___x_2046_, v___x_2034_, v_type_2019_, v_type_2019_, v_val_2041_);
v___x_2048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2047_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v_a_2049_);
v___x_2054_ = v___x_2043_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
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
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_del_object(v___x_2043_);
v_a_2060_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2048_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2048_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_dec(v_a_2037_);
lean_dec_ref_known(v___x_2032_, 2);
lean_dec_ref(v_type_2019_);
v___x_2069_ = lean_box(0);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2069_);
v___x_2071_ = v___x_2039_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2032_, 2);
lean_dec_ref(v_type_2019_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2074_, lean_object* v_type_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2074_, v_type_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2084_, lean_object* v_type_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2084_, v_type_2085_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2098_, lean_object* v_type_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2098_, v_type_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec(v_a_2100_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2112_, lean_object* v_type_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_smulType_2129_; lean_object* v___x_2130_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2123_ = lean_box(0);
lean_inc(v_u_2112_);
v___x_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_u_2112_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_u_2112_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2122_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
lean_inc_ref(v___x_2126_);
v___x_2127_ = l_Lean_mkConst(v___x_2121_, v___x_2126_);
v___x_2128_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2113_, 2);
v_smulType_2129_ = l_Lean_mkApp3(v___x_2127_, v___x_2128_, v_type_2113_, v_type_2113_);
v___x_2130_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2129_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2167_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2167_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2167_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
if (lean_obj_tag(v_a_2131_) == 1)
{
lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2133_);
v_val_2135_ = lean_ctor_get(v_a_2131_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2137_ = v_a_2131_;
v_isShared_2138_ = v_isSharedCheck_2162_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v_a_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2162_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2140_ = l_Lean_mkConst(v___x_2139_, v___x_2126_);
lean_inc_ref(v_type_2113_);
v___x_2141_ = l_Lean_mkApp4(v___x_2140_, v___x_2128_, v_type_2113_, v_type_2113_, v_val_2135_);
v___x_2142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2141_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_a_2143_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2148_);
v___x_2150_ = v___x_2145_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_del_object(v___x_2137_);
v_a_2154_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2142_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2142_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec(v_a_2131_);
lean_dec_ref_known(v___x_2126_, 2);
lean_dec_ref(v_type_2113_);
v___x_2163_ = lean_box(0);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2163_);
v___x_2165_ = v___x_2133_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2126_, 2);
lean_dec_ref(v_type_2113_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2168_, lean_object* v_type_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2168_, v_type_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2178_, lean_object* v_type_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2178_, v_type_2179_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2192_, lean_object* v_type_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2192_, v_type_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec(v_a_2194_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v_ks_2210_; lean_object* v_vs_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2235_; 
v_ks_2210_ = lean_ctor_get(v_x_2206_, 0);
v_vs_2211_ = lean_ctor_get(v_x_2206_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_x_2206_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2213_ = v_x_2206_;
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_vs_2211_);
lean_inc(v_ks_2210_);
lean_dec(v_x_2206_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2235_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_array_get_size(v_ks_2210_);
v___x_2216_ = lean_nat_dec_lt(v_x_2207_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec(v_x_2207_);
v___x_2217_ = lean_array_push(v_ks_2210_, v_x_2208_);
v___x_2218_ = lean_array_push(v_vs_2211_, v_x_2209_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2218_);
lean_ctor_set(v___x_2213_, 0, v___x_2217_);
v___x_2220_ = v___x_2213_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v_k_x27_2222_; uint8_t v___x_2223_; 
v_k_x27_2222_ = lean_array_fget_borrowed(v_ks_2210_, v_x_2207_);
v___x_2223_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2208_, v_k_x27_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2225_; 
if (v_isShared_2214_ == 0)
{
v___x_2225_ = v___x_2213_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_ks_2210_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_vs_2211_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_add(v_x_2207_, v___x_2226_);
lean_dec(v_x_2207_);
v_x_2206_ = v___x_2225_;
v_x_2207_ = v___x_2227_;
goto _start;
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_array_fset(v_ks_2210_, v_x_2207_, v_x_2208_);
v___x_2231_ = lean_array_fset(v_vs_2211_, v_x_2207_, v_x_2209_);
lean_dec(v_x_2207_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2231_);
lean_ctor_set(v___x_2213_, 0, v___x_2230_);
v___x_2233_ = v___x_2213_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2231_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2236_, lean_object* v_k_2237_, lean_object* v_v_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2236_, v___x_2239_, v_k_2237_, v_v_2238_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2242_, size_t v_x_2243_, size_t v_x_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2242_) == 0)
{
lean_object* v_es_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v_j_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_es_2247_ = lean_ctor_get(v_x_2242_, 0);
v___x_2248_ = ((size_t)31ULL);
v___x_2249_ = lean_usize_land(v_x_2243_, v___x_2248_);
v_j_2250_ = lean_usize_to_nat(v___x_2249_);
v___x_2251_ = lean_array_get_size(v_es_2247_);
v___x_2252_ = lean_nat_dec_lt(v_j_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec(v_j_2250_);
lean_dec(v_x_2246_);
lean_dec_ref(v_x_2245_);
return v_x_2242_;
}
else
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2291_; 
lean_inc_ref(v_es_2247_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_x_2242_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v_x_2242_, 0);
lean_dec(v_unused_2292_);
v___x_2254_ = v_x_2242_;
v_isShared_2255_ = v_isSharedCheck_2291_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v_x_2242_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2291_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_v_2256_; lean_object* v___x_2257_; lean_object* v_xs_x27_2258_; lean_object* v___y_2260_; 
v_v_2256_ = lean_array_fget(v_es_2247_, v_j_2250_);
v___x_2257_ = lean_box(0);
v_xs_x27_2258_ = lean_array_fset(v_es_2247_, v_j_2250_, v___x_2257_);
switch(lean_obj_tag(v_v_2256_))
{
case 0:
{
lean_object* v_key_2265_; lean_object* v_val_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2276_; 
v_key_2265_ = lean_ctor_get(v_v_2256_, 0);
v_val_2266_ = lean_ctor_get(v_v_2256_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_v_2256_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2268_ = v_v_2256_;
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_val_2266_);
lean_inc(v_key_2265_);
lean_dec(v_v_2256_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2245_, v_key_2265_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_del_object(v___x_2268_);
v___x_2271_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2265_, v_val_2266_, v_x_2245_, v_x_2246_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___y_2260_ = v___x_2272_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2274_; 
lean_dec(v_val_2266_);
lean_dec(v_key_2265_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_x_2246_);
lean_ctor_set(v___x_2268_, 0, v_x_2245_);
v___x_2274_ = v___x_2268_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_x_2245_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_x_2246_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
v___y_2260_ = v___x_2274_;
goto v___jp_2259_;
}
}
}
}
case 1:
{
lean_object* v_node_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2289_; 
v_node_2277_ = lean_ctor_get(v_v_2256_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_v_2256_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2279_ = v_v_2256_;
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_node_2277_);
lean_dec(v_v_2256_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2289_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
size_t v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2281_ = ((size_t)5ULL);
v___x_2282_ = lean_usize_shift_right(v_x_2243_, v___x_2281_);
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_add(v_x_2244_, v___x_2283_);
v___x_2285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2277_, v___x_2282_, v___x_2284_, v_x_2245_, v_x_2246_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2285_);
v___x_2287_ = v___x_2279_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
v___y_2260_ = v___x_2287_;
goto v___jp_2259_;
}
}
}
default: 
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_x_2245_);
lean_ctor_set(v___x_2290_, 1, v_x_2246_);
v___y_2260_ = v___x_2290_;
goto v___jp_2259_;
}
}
v___jp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = lean_array_fset(v_xs_x27_2258_, v_j_2250_, v___y_2260_);
lean_dec(v_j_2250_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
else
{
lean_object* v_ks_2293_; lean_object* v_vs_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2314_; 
v_ks_2293_ = lean_ctor_get(v_x_2242_, 0);
v_vs_2294_ = lean_ctor_get(v_x_2242_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_x_2242_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2296_ = v_x_2242_;
v_isShared_2297_ = v_isSharedCheck_2314_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_vs_2294_);
lean_inc(v_ks_2293_);
lean_dec(v_x_2242_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2314_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_ks_2293_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_vs_2294_);
v___x_2299_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v_newNode_2300_; uint8_t v___y_2302_; size_t v___x_2308_; uint8_t v___x_2309_; 
v_newNode_2300_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2299_, v_x_2245_, v_x_2246_);
v___x_2308_ = ((size_t)7ULL);
v___x_2309_ = lean_usize_dec_le(v___x_2308_, v_x_2244_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2300_);
v___x_2311_ = lean_unsigned_to_nat(4u);
v___x_2312_ = lean_nat_dec_lt(v___x_2310_, v___x_2311_);
lean_dec(v___x_2310_);
v___y_2302_ = v___x_2312_;
goto v___jp_2301_;
}
else
{
v___y_2302_ = v___x_2309_;
goto v___jp_2301_;
}
v___jp_2301_:
{
if (v___y_2302_ == 0)
{
lean_object* v_ks_2303_; lean_object* v_vs_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_ks_2303_ = lean_ctor_get(v_newNode_2300_, 0);
lean_inc_ref(v_ks_2303_);
v_vs_2304_ = lean_ctor_get(v_newNode_2300_, 1);
lean_inc_ref(v_vs_2304_);
lean_dec_ref(v_newNode_2300_);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2244_, v_ks_2303_, v_vs_2304_, v___x_2305_, v___x_2306_);
lean_dec_ref(v_vs_2304_);
lean_dec_ref(v_ks_2303_);
return v___x_2307_;
}
else
{
return v_newNode_2300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2315_, lean_object* v_keys_2316_, lean_object* v_vals_2317_, lean_object* v_i_2318_, lean_object* v_entries_2319_){
_start:
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_array_get_size(v_keys_2316_);
v___x_2321_ = lean_nat_dec_lt(v_i_2318_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec(v_i_2318_);
return v_entries_2319_;
}
else
{
lean_object* v_k_2322_; lean_object* v_v_2323_; uint64_t v___x_2324_; size_t v_h_2325_; size_t v___x_2326_; lean_object* v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; size_t v_h_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_k_2322_ = lean_array_fget_borrowed(v_keys_2316_, v_i_2318_);
v_v_2323_ = lean_array_fget_borrowed(v_vals_2317_, v_i_2318_);
v___x_2324_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2322_);
v_h_2325_ = lean_uint64_to_usize(v___x_2324_);
v___x_2326_ = ((size_t)5ULL);
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_sub(v_depth_2315_, v___x_2328_);
v___x_2330_ = lean_usize_mul(v___x_2326_, v___x_2329_);
v_h_2331_ = lean_usize_shift_right(v_h_2325_, v___x_2330_);
v___x_2332_ = lean_nat_add(v_i_2318_, v___x_2327_);
lean_dec(v_i_2318_);
lean_inc(v_v_2323_);
lean_inc(v_k_2322_);
v___x_2333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2319_, v_h_2331_, v_depth_2315_, v_k_2322_, v_v_2323_);
v_i_2318_ = v___x_2332_;
v_entries_2319_ = v___x_2333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2335_, lean_object* v_keys_2336_, lean_object* v_vals_2337_, lean_object* v_i_2338_, lean_object* v_entries_2339_){
_start:
{
size_t v_depth_boxed_2340_; lean_object* v_res_2341_; 
v_depth_boxed_2340_ = lean_unbox_usize(v_depth_2335_);
lean_dec(v_depth_2335_);
v_res_2341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2340_, v_keys_2336_, v_vals_2337_, v_i_2338_, v_entries_2339_);
lean_dec_ref(v_vals_2337_);
lean_dec_ref(v_keys_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v_x_575381__boxed_2347_; size_t v_x_575382__boxed_2348_; lean_object* v_res_2349_; 
v_x_575381__boxed_2347_ = lean_unbox_usize(v_x_2343_);
lean_dec(v_x_2343_);
v_x_575382__boxed_2348_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2342_, v_x_575381__boxed_2347_, v_x_575382__boxed_2348_, v_x_2345_, v_x_2346_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
uint64_t v___x_2353_; size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2351_);
v___x_2354_ = lean_uint64_to_usize(v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2350_, v___x_2354_, v___x_2355_, v_x_2351_, v_x_2352_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2357_, lean_object* v_s_2358_){
_start:
{
lean_object* v_structs_2359_; lean_object* v_typeIdOf_2360_; lean_object* v_exprToStructId_2361_; lean_object* v_exprToStructIdEntries_2362_; lean_object* v_forbiddenNatModules_2363_; lean_object* v_natStructs_2364_; lean_object* v_natTypeIdOf_2365_; lean_object* v_exprToNatStructId_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2375_; 
v_structs_2359_ = lean_ctor_get(v_s_2358_, 0);
v_typeIdOf_2360_ = lean_ctor_get(v_s_2358_, 1);
v_exprToStructId_2361_ = lean_ctor_get(v_s_2358_, 2);
v_exprToStructIdEntries_2362_ = lean_ctor_get(v_s_2358_, 3);
v_forbiddenNatModules_2363_ = lean_ctor_get(v_s_2358_, 4);
v_natStructs_2364_ = lean_ctor_get(v_s_2358_, 5);
v_natTypeIdOf_2365_ = lean_ctor_get(v_s_2358_, 6);
v_exprToNatStructId_2366_ = lean_ctor_get(v_s_2358_, 7);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_s_2358_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2368_ = v_s_2358_;
v_isShared_2369_ = v_isSharedCheck_2375_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_exprToNatStructId_2366_);
lean_inc(v_natTypeIdOf_2365_);
lean_inc(v_natStructs_2364_);
lean_inc(v_forbiddenNatModules_2363_);
lean_inc(v_exprToStructIdEntries_2362_);
lean_inc(v_exprToStructId_2361_);
lean_inc(v_typeIdOf_2360_);
lean_inc(v_structs_2359_);
lean_dec(v_s_2358_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2375_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2370_ = lean_box(0);
v___x_2371_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2363_, v_type_2357_, v___x_2370_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 4, v___x_2371_);
v___x_2373_ = v___x_2368_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_structs_2359_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_typeIdOf_2360_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_exprToStructId_2361_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_exprToStructIdEntries_2362_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2374_, 5, v_natStructs_2364_);
lean_ctor_set(v_reuseFailAlloc_2374_, 6, v_natTypeIdOf_2365_);
lean_ctor_set(v_reuseFailAlloc_2374_, 7, v_exprToNatStructId_2366_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v_a_2376_, lean_object* v_00___2377_){
_start:
{
if (lean_obj_tag(v_a_2376_) == 0)
{
uint8_t v___x_2378_; 
v___x_2378_ = 0;
return v___x_2378_;
}
else
{
uint8_t v___x_2379_; 
v___x_2379_ = 1;
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object* v_a_2380_, lean_object* v_00___2381_){
_start:
{
uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_res_2382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2380_, v_00___2381_);
lean_dec(v_a_2380_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v___x_2384_, lean_object* v_s_2385_){
_start:
{
lean_object* v_structs_2386_; lean_object* v_typeIdOf_2387_; lean_object* v_exprToStructId_2388_; lean_object* v_exprToStructIdEntries_2389_; lean_object* v_forbiddenNatModules_2390_; lean_object* v_natStructs_2391_; lean_object* v_natTypeIdOf_2392_; lean_object* v_exprToNatStructId_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2401_; 
v_structs_2386_ = lean_ctor_get(v_s_2385_, 0);
v_typeIdOf_2387_ = lean_ctor_get(v_s_2385_, 1);
v_exprToStructId_2388_ = lean_ctor_get(v_s_2385_, 2);
v_exprToStructIdEntries_2389_ = lean_ctor_get(v_s_2385_, 3);
v_forbiddenNatModules_2390_ = lean_ctor_get(v_s_2385_, 4);
v_natStructs_2391_ = lean_ctor_get(v_s_2385_, 5);
v_natTypeIdOf_2392_ = lean_ctor_get(v_s_2385_, 6);
v_exprToNatStructId_2393_ = lean_ctor_get(v_s_2385_, 7);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_s_2385_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2395_ = v_s_2385_;
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_exprToNatStructId_2393_);
lean_inc(v_natTypeIdOf_2392_);
lean_inc(v_natStructs_2391_);
lean_inc(v_forbiddenNatModules_2390_);
lean_inc(v_exprToStructIdEntries_2389_);
lean_inc(v_exprToStructId_2388_);
lean_inc(v_typeIdOf_2387_);
lean_inc(v_structs_2386_);
lean_dec(v_s_2385_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2401_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2397_ = lean_array_push(v_structs_2386_, v___x_2384_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2397_);
v___x_2399_ = v___x_2395_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_typeIdOf_2387_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_exprToStructId_2388_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_exprToStructIdEntries_2389_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_forbiddenNatModules_2390_);
lean_ctor_set(v_reuseFailAlloc_2400_, 5, v_natStructs_2391_);
lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_natTypeIdOf_2392_);
lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_exprToNatStructId_2393_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_unsigned_to_nat(32u);
v___x_2409_ = lean_mk_empty_array_with_capacity(v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = l_Lean_mkRawNatLit(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = l_Lean_Int_mkType;
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = l_Lean_Nat_mkType;
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___y_2535_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; uint8_t v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___x_2600_; 
lean_inc_ref(v_type_2522_);
v___x_2600_ = l_Lean_Meta_getDecLevel_x3f(v_type_2522_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_3518_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_3518_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_3518_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
if (lean_obj_tag(v_a_2601_) == 1)
{
lean_object* v_val_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_3513_; 
lean_del_object(v___x_2603_);
v_val_2605_ = lean_ctor_get(v_a_2601_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_a_2601_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_2607_ = v_a_2601_;
v_isShared_2608_ = v_isSharedCheck_3513_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_val_2605_);
lean_dec(v_a_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_3513_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; 
lean_inc_ref(v_type_2522_);
v___x_2609_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_3512_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_3512_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_3512_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2614_, v_val_2605_, v_type_2522_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2618_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2617_, v_val_2605_, v_type_2522_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_n(v_a_2619_, 2);
lean_dec_ref_known(v___x_2618_, 1);
lean_inc(v_a_2616_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2620_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_2619_, v_a_2616_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; uint8_t v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v_homomulFn_x3f_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; uint8_t v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v_ltFn_x3f_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_leFn_x3f_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v_charInst_x3f_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___x_3133_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
lean_inc(v_a_2616_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3133_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_2616_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
lean_inc(v_a_2616_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3135_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_2616_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
lean_inc(v_a_2616_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3137_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_2616_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; uint8_t v___y_3160_; lean_object* v___x_3247_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3247_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2525_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; uint8_t v_ring_3249_; lean_object* v___f_3250_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3328_; uint8_t v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3349_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v_ring_3249_ = lean_ctor_get_uint8(v_a_3248_, sizeof(void*)*13 + 21);
lean_dec(v_a_3248_);
lean_inc_ref(v_type_2522_);
v___f_3250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3250_, 0, v_type_2522_);
if (v_ring_3249_ == 0)
{
v___y_3349_ = v_ring_3249_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2610_, v___x_3434_);
if (v___x_3435_ == 0)
{
v___y_3349_ = v___x_3435_;
goto v___jp_3348_;
}
else
{
if (lean_obj_tag(v_a_3134_) == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v___x_3436_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3437_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3436_, v___f_3250_, v_a_2523_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3445_; 
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3437_, 0);
lean_dec(v_unused_3446_);
v___x_3439_ = v___x_3437_;
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
else
{
lean_dec(v___x_3437_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3445_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = lean_box(0);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3441_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3447_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3437_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3437_);
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
uint8_t v___x_3455_; 
v___x_3455_ = 0;
v___y_3349_ = v___x_3455_;
goto v___jp_3348_;
}
}
}
v___jp_3251_:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3254_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; uint8_t v_ring_3275_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_ring_3275_ = lean_ctor_get_uint8(v_a_3274_, sizeof(void*)*13 + 21);
lean_dec(v_a_3274_);
if (v_ring_3275_ == 0)
{
lean_dec_ref(v___f_3250_);
v___y_3140_ = v___y_3252_;
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3261_;
v___y_3149_ = v___y_3272_;
v___y_3150_ = v___y_3262_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3263_;
v___y_3154_ = v___y_3266_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3270_;
v___y_3157_ = v___y_3269_;
v___y_3158_ = v___y_3268_;
v___y_3159_ = v___y_3271_;
v___y_3160_ = v_ring_3275_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2610_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_dec_ref(v___f_3250_);
v___y_3140_ = v___y_3252_;
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3261_;
v___y_3149_ = v___y_3272_;
v___y_3150_ = v___y_3262_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3263_;
v___y_3154_ = v___y_3266_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3270_;
v___y_3157_ = v___y_3269_;
v___y_3158_ = v___y_3268_;
v___y_3159_ = v___y_3271_;
v___y_3160_ = v___x_3277_;
goto v___jp_3139_;
}
else
{
if (lean_obj_tag(v___y_3272_) == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3258_);
lean_dec(v___y_3255_);
lean_dec(v___y_3252_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v___x_3278_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3279_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3278_, v___f_3250_, v___y_3263_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3287_; 
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3279_, 0);
lean_dec(v_unused_3288_);
v___x_3281_ = v___x_3279_;
v_isShared_3282_ = v_isSharedCheck_3287_;
goto v_resetjp_3280_;
}
else
{
lean_dec(v___x_3279_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3287_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3283_ = lean_box(0);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3283_);
v___x_3285_ = v___x_3281_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3279_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3279_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_dec_ref(v___f_3250_);
v___y_3140_ = v___y_3252_;
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3261_;
v___y_3149_ = v___y_3272_;
v___y_3150_ = v___y_3262_;
v___y_3151_ = v___y_3264_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3263_;
v___y_3154_ = v___y_3266_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3270_;
v___y_3157_ = v___y_3269_;
v___y_3158_ = v___y_3268_;
v___y_3159_ = v___y_3271_;
v___y_3160_ = v___y_3260_;
goto v___jp_3139_;
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3258_);
lean_dec(v___y_3255_);
lean_dec(v___y_3252_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3297_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3273_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3273_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
v___jp_3305_:
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
v___y_3252_ = v___y_3306_;
v___y_3253_ = v___y_3307_;
v___y_3254_ = v___y_3308_;
v___y_3255_ = v___y_3309_;
v___y_3256_ = v___y_3310_;
v___y_3257_ = v___y_3311_;
v___y_3258_ = v___y_3312_;
v___y_3259_ = v___y_3313_;
v___y_3260_ = v___y_3314_;
v___y_3261_ = v___y_3315_;
v___y_3262_ = v___y_3316_;
v___y_3263_ = v___y_3319_;
v___y_3264_ = v___y_3318_;
v___y_3265_ = v___y_3317_;
v___y_3266_ = v___y_3320_;
v___y_3267_ = v___y_3321_;
v___y_3268_ = v___y_3324_;
v___y_3269_ = v___y_3323_;
v___y_3270_ = v___y_3322_;
v___y_3271_ = v___y_3325_;
v___y_3272_ = v___x_3326_;
goto v___jp_3251_;
}
v___jp_3327_:
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_box(0);
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3342_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3338_;
v___y_3311_ = v___y_3340_;
v___y_3312_ = v___y_3336_;
v___y_3313_ = v___y_3343_;
v___y_3314_ = v___y_3329_;
v___y_3315_ = v___y_3330_;
v___y_3316_ = v___y_3346_;
v___y_3317_ = v___y_3331_;
v___y_3318_ = v___y_3345_;
v___y_3319_ = v___y_3337_;
v___y_3320_ = v___y_3332_;
v___y_3321_ = v___y_3333_;
v___y_3322_ = v___y_3334_;
v___y_3323_ = v___y_3341_;
v___y_3324_ = v___y_3344_;
v___y_3325_ = v___x_3347_;
goto v___jp_3305_;
}
v___jp_3348_:
{
lean_object* v___x_3350_; 
lean_inc(v_a_2610_);
v___x_3350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2610_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_n(v_a_3351_, 2);
lean_dec_ref_known(v___x_3350_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_3351_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_n(v_a_3353_, 2);
lean_dec_ref_known(v___x_3352_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_3353_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3409_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3409_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3409_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
if (lean_obj_tag(v_a_3355_) == 1)
{
lean_object* v_val_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_del_object(v___x_3357_);
v_val_3359_ = lean_ctor_get(v_a_3355_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v_a_3355_, 1);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3360_, v_val_2605_, v_type_2522_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_n(v_a_3362_, 2);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3364_ = lean_box(0);
lean_inc_n(v_val_2605_, 3);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v_val_2605_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_inc_ref(v___x_3365_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_val_2605_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
lean_inc_ref(v___x_3366_);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_val_2605_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_inc_ref(v___x_3367_);
v___x_3368_ = l_Lean_mkConst(v___x_3363_, v___x_3367_);
lean_inc_ref_n(v_type_2522_, 3);
v___x_3369_ = l_Lean_mkApp4(v___x_3368_, v_type_2522_, v_type_2522_, v_type_2522_, v_a_3362_);
v___x_3370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3369_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3370_) == 0)
{
if (lean_obj_tag(v_a_2616_) == 1)
{
if (lean_obj_tag(v_a_3134_) == 1)
{
lean_object* v_a_3371_; lean_object* v_val_3372_; lean_object* v_val_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v_val_3372_ = lean_ctor_get(v_a_2616_, 0);
v_val_3373_ = lean_ctor_get(v_a_3134_, 0);
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3365_);
v___x_3375_ = l_Lean_mkConst(v___x_3374_, v___x_3365_);
lean_inc(v_val_3373_);
lean_inc(v_val_3372_);
lean_inc(v_a_3362_);
lean_inc_ref(v_type_2522_);
v___x_3376_ = l_Lean_mkApp4(v___x_3375_, v_type_2522_, v_a_3362_, v_val_3372_, v_val_3373_);
v___x_3377_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3376_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
if (lean_obj_tag(v_a_3378_) == 0)
{
lean_dec_ref_known(v_a_3134_, 1);
v___y_3306_ = v___x_3367_;
v___y_3307_ = v_a_2528_;
v___y_3308_ = v_a_2525_;
v___y_3309_ = v_a_3353_;
v___y_3310_ = v_a_2524_;
v___y_3311_ = v_a_2526_;
v___y_3312_ = v___x_3365_;
v___y_3313_ = v_a_2529_;
v___y_3314_ = v___y_3349_;
v___y_3315_ = v_a_3371_;
v___y_3316_ = v_a_2532_;
v___y_3317_ = v_val_3359_;
v___y_3318_ = v_a_2531_;
v___y_3319_ = v_a_2523_;
v___y_3320_ = v_a_3362_;
v___y_3321_ = v_a_3351_;
v___y_3322_ = v___x_3366_;
v___y_3323_ = v_a_2527_;
v___y_3324_ = v_a_2530_;
v___y_3325_ = v_a_3378_;
goto v___jp_3305_;
}
else
{
if (v___y_3349_ == 0)
{
v___y_3252_ = v___x_3367_;
v___y_3253_ = v_a_2528_;
v___y_3254_ = v_a_2525_;
v___y_3255_ = v_a_3353_;
v___y_3256_ = v_a_2524_;
v___y_3257_ = v_a_2526_;
v___y_3258_ = v___x_3365_;
v___y_3259_ = v_a_2529_;
v___y_3260_ = v___y_3349_;
v___y_3261_ = v_a_3371_;
v___y_3262_ = v_a_2532_;
v___y_3263_ = v_a_2523_;
v___y_3264_ = v_a_2531_;
v___y_3265_ = v_val_3359_;
v___y_3266_ = v_a_3362_;
v___y_3267_ = v_a_3351_;
v___y_3268_ = v_a_2530_;
v___y_3269_ = v_a_2527_;
v___y_3270_ = v___x_3366_;
v___y_3271_ = v_a_3378_;
v___y_3272_ = v_a_3134_;
goto v___jp_3251_;
}
else
{
lean_dec_ref_known(v_a_3134_, 1);
v___y_3306_ = v___x_3367_;
v___y_3307_ = v_a_2528_;
v___y_3308_ = v_a_2525_;
v___y_3309_ = v_a_3353_;
v___y_3310_ = v_a_2524_;
v___y_3311_ = v_a_2526_;
v___y_3312_ = v___x_3365_;
v___y_3313_ = v_a_2529_;
v___y_3314_ = v___y_3349_;
v___y_3315_ = v_a_3371_;
v___y_3316_ = v_a_2532_;
v___y_3317_ = v_val_3359_;
v___y_3318_ = v_a_2531_;
v___y_3319_ = v_a_2523_;
v___y_3320_ = v_a_3362_;
v___y_3321_ = v_a_3351_;
v___y_3322_ = v___x_3366_;
v___y_3323_ = v_a_2527_;
v___y_3324_ = v_a_2530_;
v___y_3325_ = v_a_3378_;
goto v___jp_3305_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec_ref_known(v_a_3134_, 1);
lean_dec(v_a_3371_);
lean_dec_ref_known(v_a_2616_, 1);
lean_dec_ref_known(v___x_3367_, 2);
lean_dec_ref_known(v___x_3366_, 2);
lean_dec_ref_known(v___x_3365_, 2);
lean_dec(v_a_3362_);
lean_dec(v_val_3359_);
lean_dec(v_a_3353_);
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3379_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3377_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3377_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; 
lean_dec(v_a_3134_);
v_a_3387_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3370_, 1);
v___y_3328_ = v___x_3367_;
v___y_3329_ = v___y_3349_;
v___y_3330_ = v_a_3387_;
v___y_3331_ = v_val_3359_;
v___y_3332_ = v_a_3362_;
v___y_3333_ = v_a_3351_;
v___y_3334_ = v___x_3366_;
v___y_3335_ = v_a_3353_;
v___y_3336_ = v___x_3365_;
v___y_3337_ = v_a_2523_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
v___y_3344_ = v_a_2530_;
v___y_3345_ = v_a_2531_;
v___y_3346_ = v_a_2532_;
goto v___jp_3327_;
}
}
else
{
lean_object* v_a_3388_; 
lean_dec(v_a_3134_);
v_a_3388_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3370_, 1);
v___y_3328_ = v___x_3367_;
v___y_3329_ = v___y_3349_;
v___y_3330_ = v_a_3388_;
v___y_3331_ = v_val_3359_;
v___y_3332_ = v_a_3362_;
v___y_3333_ = v_a_3351_;
v___y_3334_ = v___x_3366_;
v___y_3335_ = v_a_3353_;
v___y_3336_ = v___x_3365_;
v___y_3337_ = v_a_2523_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
v___y_3344_ = v_a_2530_;
v___y_3345_ = v_a_2531_;
v___y_3346_ = v_a_2532_;
goto v___jp_3327_;
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref_known(v___x_3367_, 2);
lean_dec_ref_known(v___x_3366_, 2);
lean_dec_ref_known(v___x_3365_, 2);
lean_dec(v_a_3362_);
lean_dec(v_val_3359_);
lean_dec(v_a_3353_);
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3389_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3370_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3370_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_val_3359_);
lean_dec(v_a_3353_);
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3397_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3361_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3361_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v___x_3405_ = lean_box(0);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3405_);
v___x_3407_ = v___x_3357_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_a_3353_);
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3410_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3354_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3354_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3351_);
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3418_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3352_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3352_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v___f_3250_);
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3426_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3350_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3350_);
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
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_a_3138_);
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3456_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3247_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3247_);
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
v___jp_3139_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc(v___y_3149_);
lean_inc(v_a_2616_);
v___x_3162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2616_, v___y_3149_, v_a_3136_, v___x_3161_, v_val_2605_, v_type_2522_, v___y_3157_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc(v_a_2616_);
v___x_3165_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2616_, v_a_3163_, v_a_3138_, v___x_3164_, v_val_2605_, v_type_2522_, v___y_3157_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3146_, 2);
v___x_3171_ = l_Lean_mkConst(v___x_3170_, v___y_3146_);
lean_inc_ref(v___y_3152_);
lean_inc_ref_n(v_type_2522_, 3);
v___x_3172_ = l_Lean_mkAppB(v___x_3171_, v_type_2522_, v___y_3152_);
v___x_3173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3175_ = l_Lean_mkConst(v___x_3174_, v___y_3146_);
lean_inc_ref(v___x_3172_);
v___x_3176_ = l_Lean_mkAppB(v___x_3175_, v_type_2522_, v___x_3172_);
lean_inc(v___y_3143_);
lean_inc(v_val_2605_);
v___x_3177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2605_, v_type_2522_, v___y_3143_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3179_, v_val_2605_, v_type_2522_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___x_3180_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2605_, v_type_2522_, v___y_3153_, v___y_3144_, v___y_3142_, v___y_3145_, v___y_3157_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 1);
lean_inc(v___y_3149_);
lean_inc(v_a_2619_);
lean_inc(v_a_2616_);
lean_inc(v_a_3178_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2605_, v_type_2522_, v_a_3178_, v_a_2616_, v_a_2619_, v___y_3149_, v___y_3157_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3184_) == 0)
{
if (lean_obj_tag(v_a_3178_) == 1)
{
lean_object* v_a_3185_; lean_object* v_val_3186_; lean_object* v___x_3187_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v_val_3186_ = lean_ctor_get(v_a_3178_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_a_3178_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_3187_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2605_, v_type_2522_, v_val_3186_, v___y_3153_, v___y_3144_, v___y_3142_, v___y_3145_, v___y_3157_, v___y_3141_, v___y_3147_, v___y_3158_, v___y_3151_, v___y_3150_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___y_2831_ = v___y_3140_;
v___y_2832_ = v___x_3168_;
v___y_2833_ = v___x_3167_;
v___y_2834_ = v___y_3143_;
v___y_2835_ = v_a_3181_;
v___y_2836_ = v___y_3146_;
v___y_2837_ = v___y_3160_;
v___y_2838_ = v___y_3148_;
v___y_2839_ = v___y_3149_;
v___y_2840_ = v___x_3172_;
v___y_2841_ = v_a_3166_;
v___y_2842_ = v___y_3152_;
v___y_2843_ = v_a_3185_;
v___y_2844_ = v___y_3154_;
v___y_2845_ = v_a_3183_;
v___y_2846_ = v___y_3155_;
v___y_2847_ = v___y_3156_;
v___y_2848_ = v___y_3159_;
v___y_2849_ = v___x_3169_;
v___y_2850_ = v___x_3176_;
v___y_2851_ = v___x_3173_;
v_charInst_x3f_2852_ = v_a_3188_;
v___y_2853_ = v___y_3153_;
v___y_2854_ = v___y_3144_;
v___y_2855_ = v___y_3142_;
v___y_2856_ = v___y_3145_;
v___y_2857_ = v___y_3157_;
v___y_2858_ = v___y_3141_;
v___y_2859_ = v___y_3147_;
v___y_2860_ = v___y_3158_;
v___y_2861_ = v___y_3151_;
v___y_2862_ = v___y_3150_;
goto v___jp_2830_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3185_);
lean_dec(v_a_3183_);
lean_dec(v_a_3181_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3166_);
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3189_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3187_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3187_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
lean_dec(v_a_3178_);
v_a_3197_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3198_ = lean_box(0);
v___y_2831_ = v___y_3140_;
v___y_2832_ = v___x_3168_;
v___y_2833_ = v___x_3167_;
v___y_2834_ = v___y_3143_;
v___y_2835_ = v_a_3181_;
v___y_2836_ = v___y_3146_;
v___y_2837_ = v___y_3160_;
v___y_2838_ = v___y_3148_;
v___y_2839_ = v___y_3149_;
v___y_2840_ = v___x_3172_;
v___y_2841_ = v_a_3166_;
v___y_2842_ = v___y_3152_;
v___y_2843_ = v_a_3197_;
v___y_2844_ = v___y_3154_;
v___y_2845_ = v_a_3183_;
v___y_2846_ = v___y_3155_;
v___y_2847_ = v___y_3156_;
v___y_2848_ = v___y_3159_;
v___y_2849_ = v___x_3169_;
v___y_2850_ = v___x_3176_;
v___y_2851_ = v___x_3173_;
v_charInst_x3f_2852_ = v___x_3198_;
v___y_2853_ = v___y_3153_;
v___y_2854_ = v___y_3144_;
v___y_2855_ = v___y_3142_;
v___y_2856_ = v___y_3145_;
v___y_2857_ = v___y_3157_;
v___y_2858_ = v___y_3141_;
v___y_2859_ = v___y_3147_;
v___y_2860_ = v___y_3158_;
v___y_2861_ = v___y_3151_;
v___y_2862_ = v___y_3150_;
goto v___jp_2830_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_a_3183_);
lean_dec(v_a_3181_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3166_);
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3199_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3184_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3184_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_a_3181_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3166_);
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3207_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3182_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3182_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3166_);
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3215_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3180_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3180_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3172_);
lean_dec(v_a_3166_);
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3223_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3177_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3177_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3231_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3165_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3165_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v___y_3159_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec(v___y_3143_);
lean_dec(v___y_3140_);
lean_dec(v_a_3138_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3239_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3162_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3162_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_a_3136_);
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3464_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3137_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3137_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_a_3134_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3472_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3135_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3135_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3480_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3133_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3133_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
v___jp_2622_:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2648_, v___y_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v_structs_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; size_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___f_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v_structs_2660_ = lean_ctor_get(v_a_2659_, 0);
lean_inc_ref(v_structs_2660_);
lean_dec(v_a_2659_);
v___x_2661_ = lean_array_get_size(v_structs_2660_);
lean_dec_ref(v_structs_2660_);
v___x_2662_ = lean_unsigned_to_nat(32u);
v___x_2663_ = lean_mk_empty_array_with_capacity(v___x_2662_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2665_ = ((size_t)5ULL);
lean_inc(v___y_2633_);
v___x_2666_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2663_);
lean_ctor_set(v___x_2666_, 2, v___y_2633_);
lean_ctor_set(v___x_2666_, 3, v___y_2633_);
lean_ctor_set_usize(v___x_2666_, 4, v___x_2665_);
v___x_2667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_box(0);
lean_inc_ref_n(v___x_2666_, 7);
lean_inc(v___y_2637_);
lean_inc(v___y_2624_);
lean_inc(v___y_2628_);
lean_inc(v___y_2636_);
lean_inc(v___y_2626_);
v___x_2670_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2661_);
lean_ctor_set(v___x_2670_, 1, v_a_2610_);
lean_ctor_set(v___x_2670_, 2, v_type_2522_);
lean_ctor_set(v___x_2670_, 3, v_val_2605_);
lean_ctor_set(v___x_2670_, 4, v___y_2635_);
lean_ctor_set(v___x_2670_, 5, v_a_2616_);
lean_ctor_set(v___x_2670_, 6, v_a_2619_);
lean_ctor_set(v___x_2670_, 7, v_a_2621_);
lean_ctor_set(v___x_2670_, 8, v___y_2632_);
lean_ctor_set(v___x_2670_, 9, v___y_2641_);
lean_ctor_set(v___x_2670_, 10, v___y_2634_);
lean_ctor_set(v___x_2670_, 11, v___y_2646_);
lean_ctor_set(v___x_2670_, 12, v___y_2626_);
lean_ctor_set(v___x_2670_, 13, v___y_2638_);
lean_ctor_set(v___x_2670_, 14, v___y_2636_);
lean_ctor_set(v___x_2670_, 15, v___y_2628_);
lean_ctor_set(v___x_2670_, 16, v___y_2624_);
lean_ctor_set(v___x_2670_, 17, v___y_2640_);
lean_ctor_set(v___x_2670_, 18, v___y_2642_);
lean_ctor_set(v___x_2670_, 19, v___y_2637_);
lean_ctor_set(v___x_2670_, 20, v___y_2623_);
lean_ctor_set(v___x_2670_, 21, v___y_2643_);
lean_ctor_set(v___x_2670_, 22, v___y_2631_);
lean_ctor_set(v___x_2670_, 23, v___y_2627_);
lean_ctor_set(v___x_2670_, 24, v___y_2644_);
lean_ctor_set(v___x_2670_, 25, v___y_2630_);
lean_ctor_set(v___x_2670_, 26, v___y_2645_);
lean_ctor_set(v___x_2670_, 27, v_homomulFn_x3f_2647_);
lean_ctor_set(v___x_2670_, 28, v___y_2625_);
lean_ctor_set(v___x_2670_, 29, v___y_2639_);
lean_ctor_set(v___x_2670_, 30, v___x_2666_);
lean_ctor_set(v___x_2670_, 31, v___x_2667_);
lean_ctor_set(v___x_2670_, 32, v___x_2666_);
lean_ctor_set(v___x_2670_, 33, v___x_2666_);
lean_ctor_set(v___x_2670_, 34, v___x_2666_);
lean_ctor_set(v___x_2670_, 35, v___x_2666_);
lean_ctor_set(v___x_2670_, 36, v___x_2668_);
lean_ctor_set(v___x_2670_, 37, v___x_2667_);
lean_ctor_set(v___x_2670_, 38, v___x_2666_);
lean_ctor_set(v___x_2670_, 39, v___x_2669_);
lean_ctor_set(v___x_2670_, 40, v___x_2666_);
lean_ctor_set(v___x_2670_, 41, v___x_2666_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*42, v___y_2629_);
v___f_2671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2671_, 0, v___x_2670_);
v___x_2672_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2673_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2672_, v___f_2671_, v___y_2648_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_dec_ref_known(v___x_2673_, 1);
if (lean_obj_tag(v___y_2637_) == 1)
{
if (lean_obj_tag(v___y_2626_) == 0)
{
lean_dec_ref_known(v___y_2637_, 1);
lean_dec(v___y_2636_);
lean_dec(v___y_2628_);
lean_dec(v___y_2624_);
v___y_2535_ = v___x_2661_;
goto v___jp_2534_;
}
else
{
lean_dec_ref_known(v___y_2626_, 1);
if (lean_obj_tag(v___y_2636_) == 0)
{
if (v___y_2629_ == 0)
{
if (lean_obj_tag(v___y_2628_) == 0)
{
lean_object* v_val_2674_; uint8_t v___x_2675_; 
v_val_2674_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_val_2674_);
lean_dec_ref_known(v___y_2637_, 1);
v___x_2675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2624_);
lean_dec(v___y_2624_);
if (v___x_2675_ == 0)
{
lean_dec(v_val_2674_);
v___y_2535_ = v___x_2661_;
goto v___jp_2534_;
}
else
{
v___y_2550_ = v___y_2648_;
v___y_2551_ = v___y_2651_;
v___y_2552_ = v___y_2650_;
v___y_2553_ = v___y_2657_;
v___y_2554_ = v_val_2674_;
v___y_2555_ = v___y_2653_;
v___y_2556_ = v___y_2654_;
v___y_2557_ = v___y_2655_;
v___y_2558_ = v___y_2649_;
v___y_2559_ = v___y_2629_;
v___y_2560_ = v___y_2652_;
v___y_2561_ = v___x_2661_;
v___y_2562_ = v___y_2656_;
goto v___jp_2549_;
}
}
else
{
lean_object* v_val_2676_; 
lean_dec_ref_known(v___y_2628_, 1);
lean_dec(v___y_2624_);
v_val_2676_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v___y_2637_, 1);
v___y_2550_ = v___y_2648_;
v___y_2551_ = v___y_2651_;
v___y_2552_ = v___y_2650_;
v___y_2553_ = v___y_2657_;
v___y_2554_ = v_val_2676_;
v___y_2555_ = v___y_2653_;
v___y_2556_ = v___y_2654_;
v___y_2557_ = v___y_2655_;
v___y_2558_ = v___y_2649_;
v___y_2559_ = v___y_2629_;
v___y_2560_ = v___y_2652_;
v___y_2561_ = v___x_2661_;
v___y_2562_ = v___y_2656_;
goto v___jp_2549_;
}
}
else
{
lean_object* v_val_2677_; 
lean_dec(v___y_2628_);
lean_dec(v___y_2624_);
v_val_2677_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v___y_2637_, 1);
v___y_2575_ = v___y_2648_;
v___y_2576_ = v___y_2651_;
v___y_2577_ = v___y_2650_;
v___y_2578_ = v___y_2657_;
v___y_2579_ = v_val_2677_;
v___y_2580_ = v___y_2653_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2649_;
v___y_2584_ = v___y_2629_;
v___y_2585_ = v___y_2652_;
v___y_2586_ = v___x_2661_;
v___y_2587_ = v___y_2656_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_val_2678_; 
lean_dec_ref_known(v___y_2636_, 1);
lean_dec(v___y_2628_);
lean_dec(v___y_2624_);
v_val_2678_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_val_2678_);
lean_dec_ref_known(v___y_2637_, 1);
v___y_2575_ = v___y_2648_;
v___y_2576_ = v___y_2651_;
v___y_2577_ = v___y_2650_;
v___y_2578_ = v___y_2657_;
v___y_2579_ = v_val_2678_;
v___y_2580_ = v___y_2653_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2649_;
v___y_2584_ = v___y_2629_;
v___y_2585_ = v___y_2652_;
v___y_2586_ = v___x_2661_;
v___y_2587_ = v___y_2656_;
goto v___jp_2574_;
}
}
}
else
{
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2628_);
lean_dec(v___y_2626_);
lean_dec(v___y_2624_);
v___y_2535_ = v___x_2661_;
goto v___jp_2534_;
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2628_);
lean_dec(v___y_2626_);
lean_dec(v___y_2624_);
v_a_2679_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2673_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2673_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_homomulFn_x3f_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_dec(v_a_2610_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2687_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2658_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2658_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2730_; 
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2605_, v_type_2522_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2732_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2605_, v_type_2522_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2732_) == 0)
{
if (lean_obj_tag(v___y_2712_) == 0)
{
lean_object* v_a_2733_; 
lean_dec(v___y_2696_);
lean_del_object(v___x_2607_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___y_2623_ = v___y_2697_;
v___y_2624_ = v___y_2698_;
v___y_2625_ = v___y_2699_;
v___y_2626_ = v___y_2701_;
v___y_2627_ = v___y_2702_;
v___y_2628_ = v___y_2703_;
v___y_2629_ = v___y_2704_;
v___y_2630_ = v_a_2731_;
v___y_2631_ = v___y_2705_;
v___y_2632_ = v___y_2706_;
v___y_2633_ = v___y_2707_;
v___y_2634_ = v___y_2708_;
v___y_2635_ = v___y_2709_;
v___y_2636_ = v___y_2710_;
v___y_2637_ = v___y_2711_;
v___y_2638_ = v___y_2712_;
v___y_2639_ = v___y_2714_;
v___y_2640_ = v___y_2713_;
v___y_2641_ = v___y_2716_;
v___y_2642_ = v___y_2715_;
v___y_2643_ = v_ltFn_x3f_2719_;
v___y_2644_ = v___y_2717_;
v___y_2645_ = v_a_2733_;
v___y_2646_ = v___y_2718_;
v_homomulFn_x3f_2647_ = v___y_2700_;
v___y_2648_ = v___y_2720_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2729_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v___y_2700_);
v_a_2734_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2735_, v_val_2605_, v_type_2522_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2739_ = l_Lean_mkConst(v___x_2738_, v___y_2696_);
lean_inc_ref_n(v_type_2522_, 3);
v___x_2740_ = l_Lean_mkApp4(v___x_2739_, v_type_2522_, v_type_2522_, v_type_2522_, v_a_2737_);
v___x_2741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2740_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v_a_2742_);
v___x_2744_ = v___x_2607_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
v___y_2623_ = v___y_2697_;
v___y_2624_ = v___y_2698_;
v___y_2625_ = v___y_2699_;
v___y_2626_ = v___y_2701_;
v___y_2627_ = v___y_2702_;
v___y_2628_ = v___y_2703_;
v___y_2629_ = v___y_2704_;
v___y_2630_ = v_a_2731_;
v___y_2631_ = v___y_2705_;
v___y_2632_ = v___y_2706_;
v___y_2633_ = v___y_2707_;
v___y_2634_ = v___y_2708_;
v___y_2635_ = v___y_2709_;
v___y_2636_ = v___y_2710_;
v___y_2637_ = v___y_2711_;
v___y_2638_ = v___y_2712_;
v___y_2639_ = v___y_2714_;
v___y_2640_ = v___y_2713_;
v___y_2641_ = v___y_2716_;
v___y_2642_ = v___y_2715_;
v___y_2643_ = v_ltFn_x3f_2719_;
v___y_2644_ = v___y_2717_;
v___y_2645_ = v_a_2734_;
v___y_2646_ = v___y_2718_;
v_homomulFn_x3f_2647_ = v___x_2744_;
v___y_2648_ = v___y_2720_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2729_;
goto v___jp_2622_;
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref_known(v___y_2712_, 1);
lean_dec(v_a_2734_);
lean_dec(v_a_2731_);
lean_dec(v_ltFn_x3f_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2746_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2741_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2741_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec_ref_known(v___y_2712_, 1);
lean_dec(v_a_2734_);
lean_dec(v_a_2731_);
lean_dec(v_ltFn_x3f_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2754_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2736_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2736_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2731_);
lean_dec(v_ltFn_x3f_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2762_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2732_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2732_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_ltFn_x3f_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2770_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2730_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2730_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
v___jp_2778_:
{
if (lean_obj_tag(v_a_2619_) == 1)
{
lean_object* v_val_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_val_2813_ = lean_ctor_get(v_a_2619_, 0);
v___x_2814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2815_ = l_Lean_mkConst(v___x_2814_, v___y_2786_);
lean_inc(v_val_2813_);
lean_inc_ref(v_type_2522_);
v___x_2816_ = l_Lean_mkAppB(v___x_2815_, v_type_2522_, v_val_2813_);
v___x_2817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2816_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 0, v_a_2818_);
v___x_2820_ = v___x_2612_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
v___y_2696_ = v___y_2779_;
v___y_2697_ = v_leFn_x3f_2802_;
v___y_2698_ = v___y_2780_;
v___y_2699_ = v___y_2781_;
v___y_2700_ = v___y_2782_;
v___y_2701_ = v___y_2783_;
v___y_2702_ = v___y_2784_;
v___y_2703_ = v___y_2785_;
v___y_2704_ = v___y_2787_;
v___y_2705_ = v___y_2788_;
v___y_2706_ = v___y_2789_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v___y_2791_;
v___y_2709_ = v___y_2793_;
v___y_2710_ = v___y_2792_;
v___y_2711_ = v___y_2794_;
v___y_2712_ = v___y_2795_;
v___y_2713_ = v___y_2797_;
v___y_2714_ = v___y_2796_;
v___y_2715_ = v___y_2799_;
v___y_2716_ = v___y_2798_;
v___y_2717_ = v___y_2800_;
v___y_2718_ = v___y_2801_;
v_ltFn_x3f_2719_ = v___x_2820_;
v___y_2720_ = v___y_2803_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
goto v___jp_2695_;
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref_known(v_a_2619_, 1);
lean_dec(v_leFn_x3f_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec(v_a_2621_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2822_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2817_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2817_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_dec(v___y_2786_);
lean_del_object(v___x_2612_);
lean_inc(v___y_2782_);
v___y_2696_ = v___y_2779_;
v___y_2697_ = v_leFn_x3f_2802_;
v___y_2698_ = v___y_2780_;
v___y_2699_ = v___y_2781_;
v___y_2700_ = v___y_2782_;
v___y_2701_ = v___y_2783_;
v___y_2702_ = v___y_2784_;
v___y_2703_ = v___y_2785_;
v___y_2704_ = v___y_2787_;
v___y_2705_ = v___y_2788_;
v___y_2706_ = v___y_2789_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v___y_2791_;
v___y_2709_ = v___y_2793_;
v___y_2710_ = v___y_2792_;
v___y_2711_ = v___y_2794_;
v___y_2712_ = v___y_2795_;
v___y_2713_ = v___y_2797_;
v___y_2714_ = v___y_2796_;
v___y_2715_ = v___y_2799_;
v___y_2716_ = v___y_2798_;
v___y_2717_ = v___y_2800_;
v___y_2718_ = v___y_2801_;
v_ltFn_x3f_2719_ = v___y_2782_;
v___y_2720_ = v___y_2803_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
goto v___jp_2695_;
}
}
v___jp_2830_:
{
lean_object* v___x_2863_; 
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2605_, v_type_2522_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2865_, v_val_2605_, v_type_2522_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc_n(v_a_2867_, 2);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2836_);
v___x_2869_ = l_Lean_mkConst(v___x_2868_, v___y_2836_);
lean_inc_ref(v_type_2522_);
v___x_2870_ = l_Lean_mkAppB(v___x_2869_, v_type_2522_, v_a_2867_);
v___x_2871_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2870_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2836_);
v___x_2874_ = l_Lean_mkConst(v___x_2873_, v___y_2836_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2522_);
v___x_2877_ = l_Lean_mkAppB(v___x_2874_, v_type_2522_, v___x_2876_);
v___x_2878_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2877_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_3100_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_3100_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_3100_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
if (lean_obj_tag(v_a_2879_) == 1)
{
lean_object* v_val_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_3095_; 
lean_del_object(v___x_2881_);
v_val_2883_ = lean_ctor_get(v_a_2879_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_2885_ = v_a_2879_;
v_isShared_2886_ = v_isSharedCheck_3095_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_val_2883_);
lean_dec(v_a_2879_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_3095_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2836_);
v___x_2888_ = l_Lean_mkConst(v___x_2887_, v___y_2836_);
lean_inc_ref(v_type_2522_);
v___x_2889_ = l_Lean_mkApp3(v___x_2888_, v_type_2522_, v___x_2876_, v_val_2883_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2889_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_n(v_a_2891_, 2);
lean_dec_ref_known(v___x_2890_, 1);
lean_inc(v_a_2872_);
v___x_2892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2872_, v_a_2891_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2892_, 1);
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2893_, v_val_2605_, v_type_2522_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc_n(v_a_2895_, 2);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2831_);
v___x_2897_ = l_Lean_mkConst(v___x_2896_, v___y_2831_);
lean_inc_ref_n(v_type_2522_, 3);
v___x_2898_ = l_Lean_mkApp4(v___x_2897_, v_type_2522_, v_type_2522_, v_type_2522_, v_a_2895_);
v___x_2899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2898_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2902_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2901_, v_val_2605_, v_type_2522_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc_n(v_a_2903_, 2);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2836_);
v___x_2905_ = l_Lean_mkConst(v___x_2904_, v___y_2836_);
lean_inc_ref(v_type_2522_);
v___x_2906_ = l_Lean_mkAppB(v___x_2905_, v_type_2522_, v_a_2903_);
v___x_2907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2906_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2909_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2605_, v_type_2522_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc_n(v_a_2910_, 2);
lean_dec_ref_known(v___x_2909_, 1);
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___y_2847_);
v___x_2914_ = l_Lean_mkConst(v___x_2911_, v___x_2913_);
v___x_2915_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2522_, 2);
lean_inc_ref(v___x_2914_);
v___x_2916_ = l_Lean_mkApp4(v___x_2914_, v___x_2915_, v_type_2522_, v_type_2522_, v_a_2910_);
v___x_2917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2916_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2605_, v_type_2522_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_n(v_a_2920_, 2);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2522_, 2);
v___x_2922_ = l_Lean_mkApp4(v___x_2914_, v___x_2921_, v_type_2522_, v_type_2522_, v_a_2920_);
v___x_2923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2922_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2927_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___x_2925_, v___x_2926_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc_ref(v___y_2850_);
v___x_2928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2867_, v___y_2850_, v___x_2927_, v_val_2605_, v_type_2522_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2930_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___x_2925_, v___x_2929_);
v___x_2931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_2932_ = lean_box(0);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2844_, v___y_2850_, v___x_2930_, v___x_2931_, v_val_2605_, v_type_2522_, v___x_2932_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec_ref_known(v___x_2933_, 1);
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2851_);
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2935_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___y_2851_, v___x_2934_);
v___x_2936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc_ref(v___y_2840_);
v___x_2937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2895_, v___y_2840_, v___x_2935_, v___x_2936_, v_val_2605_, v_type_2522_, v___x_2932_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec_ref_known(v___x_2937_, 1);
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2851_);
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2939_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___y_2851_, v___x_2938_);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
v___x_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2903_, v___y_2840_, v___x_2939_, v_val_2605_, v_type_2522_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec_ref_known(v___x_2940_, 1);
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2849_);
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2942_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___y_2849_, v___x_2941_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_2944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc_ref(v___y_2842_);
v___x_2945_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2910_, v___y_2842_, v___x_2942_, v___x_2943_, v_val_2605_, v_type_2522_, v___x_2944_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2945_, 1);
v___x_2946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2849_);
lean_inc_ref(v___y_2832_);
lean_inc_ref(v___y_2833_);
v___x_2947_ = l_Lean_Name_mkStr4(v___y_2833_, v___y_2832_, v___y_2849_, v___x_2946_);
v___x_2948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2522_);
lean_inc(v_val_2605_);
lean_inc_ref(v___y_2842_);
v___x_2949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2920_, v___y_2842_, v___x_2947_, v___x_2943_, v_val_2605_, v_type_2522_, v___x_2948_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_dec_ref_known(v___x_2949_, 1);
if (lean_obj_tag(v_a_2616_) == 1)
{
lean_object* v_val_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_val_2950_ = lean_ctor_get(v_a_2616_, 0);
v___x_2951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2836_);
v___x_2952_ = l_Lean_mkConst(v___x_2951_, v___y_2836_);
lean_inc(v_val_2950_);
lean_inc_ref(v_type_2522_);
v___x_2953_ = l_Lean_mkAppB(v___x_2952_, v_type_2522_, v_val_2950_);
v___x_2954_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2953_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v_a_2955_);
v___x_2957_ = v___x_2885_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
v___y_2779_ = v___y_2831_;
v___y_2780_ = v_charInst_x3f_2852_;
v___y_2781_ = v_a_2900_;
v___y_2782_ = v___x_2932_;
v___y_2783_ = v___y_2834_;
v___y_2784_ = v_a_2918_;
v___y_2785_ = v___y_2835_;
v___y_2786_ = v___y_2836_;
v___y_2787_ = v___y_2837_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2839_;
v___y_2790_ = v___x_2875_;
v___y_2791_ = v___y_2841_;
v___y_2792_ = v___y_2843_;
v___y_2793_ = v___y_2842_;
v___y_2794_ = v___y_2845_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v_a_2908_;
v___y_2797_ = v_a_2872_;
v___y_2798_ = v___y_2848_;
v___y_2799_ = v_a_2891_;
v___y_2800_ = v_a_2924_;
v___y_2801_ = v_a_2864_;
v_leFn_x3f_2802_ = v___x_2957_;
v___y_2803_ = v___y_2853_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
v___y_2810_ = v___y_2860_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2862_;
goto v___jp_2778_;
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref_known(v_a_2616_, 1);
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec(v_a_2908_);
lean_dec(v_a_2900_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2959_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2954_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2954_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_del_object(v___x_2885_);
v___y_2779_ = v___y_2831_;
v___y_2780_ = v_charInst_x3f_2852_;
v___y_2781_ = v_a_2900_;
v___y_2782_ = v___x_2932_;
v___y_2783_ = v___y_2834_;
v___y_2784_ = v_a_2918_;
v___y_2785_ = v___y_2835_;
v___y_2786_ = v___y_2836_;
v___y_2787_ = v___y_2837_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2839_;
v___y_2790_ = v___x_2875_;
v___y_2791_ = v___y_2841_;
v___y_2792_ = v___y_2843_;
v___y_2793_ = v___y_2842_;
v___y_2794_ = v___y_2845_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v_a_2908_;
v___y_2797_ = v_a_2872_;
v___y_2798_ = v___y_2848_;
v___y_2799_ = v_a_2891_;
v___y_2800_ = v_a_2924_;
v___y_2801_ = v_a_2864_;
v_leFn_x3f_2802_ = v___x_2932_;
v___y_2803_ = v___y_2853_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
v___y_2810_ = v___y_2860_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2862_;
goto v___jp_2778_;
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2918_);
lean_dec(v_a_2908_);
lean_dec(v_a_2900_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2967_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2949_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2949_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2908_);
lean_dec(v_a_2900_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2975_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2945_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2945_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2900_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2983_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2940_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2940_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2991_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2937_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2937_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_2999_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2933_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2933_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_a_2924_);
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3007_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2928_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2928_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_a_2920_);
lean_dec(v_a_2918_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3015_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2923_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2923_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2914_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3023_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2919_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2919_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___x_2914_);
lean_dec(v_a_2910_);
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3031_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2917_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2917_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_a_2908_);
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3039_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_2909_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_2909_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_2903_);
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3047_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2907_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2907_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_2900_);
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3055_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2902_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2902_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_2895_);
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3063_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2899_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2899_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3071_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2894_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2894_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_2891_);
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3079_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2892_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2892_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_del_object(v___x_2885_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3087_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2890_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2890_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_dec(v_a_2879_);
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v___x_3096_ = lean_box(0);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_3096_);
v___x_3098_ = v___x_2881_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
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
lean_dec(v_a_2872_);
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3101_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_2878_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_2878_);
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
lean_dec(v_a_2867_);
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3109_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2871_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2871_);
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
lean_dec(v_a_2864_);
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3117_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_2866_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_2866_);
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
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_charInst_x3f_2852_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2831_);
lean_dec(v_a_2621_);
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3125_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_2863_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_2863_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_a_2619_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3488_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_2620_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_2620_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_a_2616_);
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3496_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_2618_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_2618_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_del_object(v___x_2612_);
lean_dec(v_a_2610_);
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
v_a_3504_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_2615_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_2615_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
else
{
lean_del_object(v___x_2607_);
lean_dec(v_val_2605_);
lean_dec_ref(v_type_2522_);
return v___x_2609_;
}
}
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_type_2522_);
v___x_3514_ = lean_box(0);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_3514_);
v___x_3516_ = v___x_2603_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v_type_2522_);
v_a_3519_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_2600_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_2600_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2535_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
v___jp_2538_:
{
if (lean_obj_tag(v___y_2540_) == 0)
{
lean_dec_ref_known(v___y_2540_, 1);
v___y_2535_ = v___y_2539_;
goto v___jp_2534_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v___y_2539_);
v_a_2541_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___y_2540_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___y_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
v___jp_2549_:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2554_, v___y_2559_, v___y_2561_, v___y_2550_, v___y_2558_, v___y_2552_, v___y_2551_, v___y_2560_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2562_, v___y_2553_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2564_, v___y_2561_, v___y_2550_);
v___y_2539_ = v___y_2561_;
v___y_2540_ = v___x_2565_;
goto v___jp_2538_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v___y_2561_);
v_a_2566_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2563_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
v___jp_2574_:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2579_, v___y_2584_, v___y_2586_, v___y_2575_, v___y_2583_, v___y_2577_, v___y_2576_, v___y_2585_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2587_, v___y_2578_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc_n(v_a_2589_, 2);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2589_, v___y_2586_, v___y_2575_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref_known(v___x_2590_, 1);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2589_, v___y_2586_, v___y_2575_);
v___y_2539_ = v___y_2586_;
v___y_2540_ = v___x_2591_;
goto v___jp_2538_;
}
else
{
lean_dec(v_a_2589_);
v___y_2539_ = v___y_2586_;
v___y_2540_ = v___x_2590_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v___y_2586_);
v_a_2592_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2588_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2588_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec(v_a_3528_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3541_, v_x_3542_, v_x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3545_, lean_object* v_x_3546_, size_t v_x_3547_, size_t v_x_3548_, lean_object* v_x_3549_, lean_object* v_x_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3546_, v_x_3547_, v_x_3548_, v_x_3549_, v_x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
size_t v_x_577967__boxed_3558_; size_t v_x_577968__boxed_3559_; lean_object* v_res_3560_; 
v_x_577967__boxed_3558_ = lean_unbox_usize(v_x_3554_);
lean_dec(v_x_3554_);
v_x_577968__boxed_3559_ = lean_unbox_usize(v_x_3555_);
lean_dec(v_x_3555_);
v_res_3560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3552_, v_x_3553_, v_x_577967__boxed_3558_, v_x_577968__boxed_3559_, v_x_3556_, v_x_3557_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3561_, lean_object* v_n_3562_, lean_object* v_k_3563_, lean_object* v_v_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3562_, v_k_3563_, v_v_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3566_, size_t v_depth_3567_, lean_object* v_keys_3568_, lean_object* v_vals_3569_, lean_object* v_heq_3570_, lean_object* v_i_3571_, lean_object* v_entries_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3567_, v_keys_3568_, v_vals_3569_, v_i_3571_, v_entries_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3574_, lean_object* v_depth_3575_, lean_object* v_keys_3576_, lean_object* v_vals_3577_, lean_object* v_heq_3578_, lean_object* v_i_3579_, lean_object* v_entries_3580_){
_start:
{
size_t v_depth_boxed_3581_; lean_object* v_res_3582_; 
v_depth_boxed_3581_ = lean_unbox_usize(v_depth_3575_);
lean_dec(v_depth_3575_);
v_res_3582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3574_, v_depth_boxed_3581_, v_keys_3576_, v_vals_3577_, v_heq_3578_, v_i_3579_, v_entries_3580_);
lean_dec_ref(v_vals_3577_);
lean_dec_ref(v_keys_3576_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3584_, v_x_3585_, v_x_3586_, v_x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3589_, lean_object* v_base_3590_, lean_object* v_natModuleInst_3591_, lean_object* v_declName_3592_, lean_object* v_le_3593_, lean_object* v_mid_3594_, lean_object* v_ord_3595_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3596_ = lean_box(0);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_val_3589_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Lean_mkConst(v_declName_3592_, v___x_3597_);
v___x_3599_ = l_Lean_mkApp5(v___x_3598_, v_base_3590_, v_natModuleInst_3591_, v_le_3593_, v_mid_3594_, v_ord_3595_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3699_, lean_object* v_base_3700_, lean_object* v_natModuleInst_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; 
lean_inc_ref(v_base_3700_);
v___x_3713_ = l_Lean_Meta_getDecLevel_x3f(v_base_3700_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_4451_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_4451_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_4451_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
if (lean_obj_tag(v_a_3714_) == 1)
{
lean_object* v_val_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_4446_; 
lean_del_object(v___x_3716_);
v_val_3718_ = lean_ctor_get(v_a_3714_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v_a_3714_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_3720_ = v_a_3714_;
v_isShared_3721_ = v_isSharedCheck_4446_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_val_3718_);
lean_dec(v_a_3714_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_4446_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v_a_3742_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v_a_3814_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___x_4032_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v_noNatDivInstQ_x3f_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v_isLinearInstQ_x3f_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___x_4287_; 
v___x_4032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4287_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4032_, v_val_3718_, v_base_3700_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc_n(v_a_4288_, 2);
lean_dec_ref_known(v___x_4287_, 1);
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4289_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_3718_, v_base_3700_, v_a_4288_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v_fst_4304_; lean_object* v_snd_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v_orderedAddInst_x3f_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
if (lean_obj_tag(v_a_4288_) == 1)
{
if (lean_obj_tag(v_a_4290_) == 1)
{
lean_object* v_val_4402_; lean_object* v_val_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_val_4402_ = lean_ctor_get(v_a_4288_, 0);
v_val_4403_ = lean_ctor_get(v_a_4290_, 0);
v___x_4404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4404_, v_val_3718_, v_base_3700_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4408_ = lean_box(0);
lean_inc(v_val_3718_);
v___x_4409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_val_3718_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l_Lean_mkConst(v___x_4407_, v___x_4409_);
lean_inc(v_val_4403_);
lean_inc(v_val_4402_);
lean_inc_ref(v_base_3700_);
v___x_4411_ = l_Lean_mkApp4(v___x_4410_, v_base_3700_, v_a_4406_, v_val_4402_, v_val_4403_);
v___x_4412_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4411_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v_orderedAddInst_x3f_4343_ = v_a_4413_;
v___y_4344_ = v_a_3702_;
v___y_4345_ = v_a_3703_;
v___y_4346_ = v_a_3704_;
v___y_4347_ = v_a_3705_;
v___y_4348_ = v_a_3706_;
v___y_4349_ = v_a_3707_;
v___y_4350_ = v_a_3708_;
v___y_4351_ = v_a_3709_;
v___y_4352_ = v_a_3710_;
v___y_4353_ = v_a_3711_;
goto v___jp_4342_;
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec_ref_known(v_a_4290_, 1);
lean_dec_ref_known(v_a_4288_, 1);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4414_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4412_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4412_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec_ref_known(v_a_4290_, 1);
lean_dec_ref_known(v_a_4288_, 1);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4422_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4405_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4405_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
v___y_4391_ = v_a_3702_;
v___y_4392_ = v_a_3703_;
v___y_4393_ = v_a_3704_;
v___y_4394_ = v_a_3705_;
v___y_4395_ = v_a_3706_;
v___y_4396_ = v_a_3707_;
v___y_4397_ = v_a_3708_;
v___y_4398_ = v_a_3709_;
v___y_4399_ = v_a_3710_;
v___y_4400_ = v_a_3711_;
goto v___jp_4390_;
}
}
else
{
v___y_4391_ = v_a_3702_;
v___y_4392_ = v_a_3703_;
v___y_4393_ = v_a_3704_;
v___y_4394_ = v_a_3705_;
v___y_4395_ = v_a_3706_;
v___y_4396_ = v_a_3707_;
v___y_4397_ = v_a_3708_;
v___y_4398_ = v_a_3709_;
v___y_4399_ = v_a_3710_;
v___y_4400_ = v_a_3711_;
goto v___jp_4390_;
}
v___jp_4291_:
{
lean_object* v___x_4309_; 
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4309_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_3718_, v_base_3700_, v_a_4288_, v___y_4300_, v___y_4303_, v___y_4306_, v___y_4292_, v___y_4299_, v___y_4294_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
if (lean_obj_tag(v_a_4310_) == 0)
{
lean_dec_ref(v_snd_4305_);
lean_dec_ref(v_fst_4304_);
v___y_4214_ = v___y_4302_;
v___y_4215_ = v___y_4293_;
v___y_4216_ = v___y_4295_;
v___y_4217_ = v___y_4296_;
v___y_4218_ = v___y_4308_;
v_isLinearInstQ_x3f_4219_ = v_a_4310_;
v___y_4220_ = v___y_4301_;
v___y_4221_ = v___y_4297_;
v___y_4222_ = v___y_4307_;
v___y_4223_ = v___y_4298_;
v___y_4224_ = v___y_4300_;
v___y_4225_ = v___y_4303_;
v___y_4226_ = v___y_4306_;
v___y_4227_ = v___y_4292_;
v___y_4228_ = v___y_4299_;
v___y_4229_ = v___y_4294_;
goto v___jp_4213_;
}
else
{
lean_object* v_val_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4320_; 
v_val_4311_ = lean_ctor_get(v_a_4310_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_a_4310_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4313_ = v_a_4310_;
v_isShared_4314_ = v_isSharedCheck_4320_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_val_4311_);
lean_dec(v_a_4310_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4320_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3701_);
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3718_, v_base_3700_, v_natModuleInst_3701_, v___x_4315_, v_fst_4304_, v_val_4311_, v_snd_4305_);
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 0, v___x_4316_);
v___x_4318_ = v___x_4313_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
v___y_4214_ = v___y_4302_;
v___y_4215_ = v___y_4293_;
v___y_4216_ = v___y_4295_;
v___y_4217_ = v___y_4296_;
v___y_4218_ = v___y_4308_;
v_isLinearInstQ_x3f_4219_ = v___x_4318_;
v___y_4220_ = v___y_4301_;
v___y_4221_ = v___y_4297_;
v___y_4222_ = v___y_4307_;
v___y_4223_ = v___y_4298_;
v___y_4224_ = v___y_4300_;
v___y_4225_ = v___y_4303_;
v___y_4226_ = v___y_4306_;
v___y_4227_ = v___y_4292_;
v___y_4228_ = v___y_4299_;
v___y_4229_ = v___y_4294_;
goto v___jp_4213_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v___y_4308_);
lean_dec_ref(v_snd_4305_);
lean_dec_ref(v_fst_4304_);
lean_dec(v___y_4302_);
lean_dec(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4293_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4321_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4309_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4309_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
v___jp_4329_:
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_box(0);
v___y_4214_ = v___x_4341_;
v___y_4215_ = v___x_4341_;
v___y_4216_ = v___x_4341_;
v___y_4217_ = v___x_4341_;
v___y_4218_ = v___x_4341_;
v_isLinearInstQ_x3f_4219_ = v___x_4341_;
v___y_4220_ = v___y_4338_;
v___y_4221_ = v___y_4333_;
v___y_4222_ = v___y_4339_;
v___y_4223_ = v___y_4335_;
v___y_4224_ = v___y_4337_;
v___y_4225_ = v___y_4331_;
v___y_4226_ = v___y_4334_;
v___y_4227_ = v___y_4330_;
v___y_4228_ = v___y_4336_;
v___y_4229_ = v___y_4332_;
goto v___jp_4213_;
}
v___jp_4342_:
{
if (lean_obj_tag(v_a_4288_) == 0)
{
lean_object* v___x_4354_; 
lean_dec(v_orderedAddInst_x3f_4343_);
lean_dec(v_a_4290_);
v___x_4354_ = lean_box(0);
v___y_4330_ = v___y_4351_;
v___y_4331_ = v___y_4349_;
v___y_4332_ = v___y_4353_;
v___y_4333_ = v___y_4345_;
v___y_4334_ = v___y_4350_;
v___y_4335_ = v___y_4347_;
v___y_4336_ = v___y_4352_;
v___y_4337_ = v___y_4348_;
v___y_4338_ = v___y_4344_;
v___y_4339_ = v___y_4346_;
v___y_4340_ = v___x_4354_;
goto v___jp_4329_;
}
else
{
if (lean_obj_tag(v_a_4290_) == 0)
{
lean_object* v___x_4355_; 
lean_dec_ref_known(v_a_4288_, 1);
lean_dec(v_orderedAddInst_x3f_4343_);
v___x_4355_ = lean_box(0);
v___y_4330_ = v___y_4351_;
v___y_4331_ = v___y_4349_;
v___y_4332_ = v___y_4353_;
v___y_4333_ = v___y_4345_;
v___y_4334_ = v___y_4350_;
v___y_4335_ = v___y_4347_;
v___y_4336_ = v___y_4352_;
v___y_4337_ = v___y_4348_;
v___y_4338_ = v___y_4344_;
v___y_4339_ = v___y_4346_;
v___y_4340_ = v___x_4355_;
goto v___jp_4329_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4343_) == 0)
{
lean_object* v___x_4356_; 
lean_dec_ref_known(v_a_4290_, 1);
lean_dec_ref_known(v_a_4288_, 1);
v___x_4356_ = lean_box(0);
v___y_4330_ = v___y_4351_;
v___y_4331_ = v___y_4349_;
v___y_4332_ = v___y_4353_;
v___y_4333_ = v___y_4345_;
v___y_4334_ = v___y_4350_;
v___y_4335_ = v___y_4347_;
v___y_4336_ = v___y_4352_;
v___y_4337_ = v___y_4348_;
v___y_4338_ = v___y_4344_;
v___y_4339_ = v___y_4346_;
v___y_4340_ = v___x_4356_;
goto v___jp_4329_;
}
else
{
lean_object* v_val_4357_; lean_object* v_val_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4389_; 
v_val_4357_ = lean_ctor_get(v_a_4288_, 0);
v_val_4358_ = lean_ctor_get(v_a_4290_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_a_4290_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4360_ = v_a_4290_;
v_isShared_4361_ = v_isSharedCheck_4389_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_val_4358_);
lean_dec(v_a_4290_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4389_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_val_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4388_; 
v_val_4362_ = lean_ctor_get(v_orderedAddInst_x3f_4343_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_orderedAddInst_x3f_4343_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4364_ = v_orderedAddInst_x3f_4343_;
v_isShared_4365_ = v_isSharedCheck_4388_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_val_4362_);
lean_dec(v_orderedAddInst_x3f_4343_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4388_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4362_);
lean_inc(v_val_4358_);
lean_inc(v_val_4357_);
lean_inc_ref(v_natModuleInst_3701_);
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3718_, v_base_3700_, v_natModuleInst_3701_, v___x_4366_, v_val_4357_, v_val_4358_, v_val_4362_);
lean_inc_ref(v___x_4367_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4367_);
v___x_4369_ = v___x_4364_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4362_);
lean_inc(v_val_4358_);
lean_inc(v_val_4357_);
lean_inc_ref(v_natModuleInst_3701_);
lean_inc_ref(v_base_3700_);
lean_inc(v_val_3718_);
v___x_4371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3718_, v_base_3700_, v_natModuleInst_3701_, v___x_4370_, v_val_4357_, v_val_4358_, v_val_4362_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4371_);
v___x_4373_ = v___x_4360_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4362_, 2);
lean_inc(v_val_4358_);
lean_inc_n(v_val_4357_, 3);
lean_inc_ref_n(v_natModuleInst_3701_, 2);
lean_inc_ref_n(v_base_3700_, 2);
lean_inc_n(v_val_3718_, 3);
v___x_4375_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3718_, v_base_3700_, v_natModuleInst_3701_, v___x_4374_, v_val_4357_, v_val_4358_, v_val_4362_);
v___x_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
v___x_4377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3718_, v_base_3700_, v_natModuleInst_3701_, v___x_4377_, v_val_4357_, v_val_4358_, v_val_4362_);
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4381_ = lean_box(0);
v___x_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_val_3718_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = l_Lean_mkConst(v___x_4380_, v___x_4382_);
lean_inc_ref(v_type_3699_);
v___x_4384_ = l_Lean_mkAppB(v___x_4383_, v_type_3699_, v___x_4367_);
v___x_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
v___y_4292_ = v___y_4351_;
v___y_4293_ = v___x_4373_;
v___y_4294_ = v___y_4353_;
v___y_4295_ = v___x_4379_;
v___y_4296_ = v___x_4376_;
v___y_4297_ = v___y_4345_;
v___y_4298_ = v___y_4347_;
v___y_4299_ = v___y_4352_;
v___y_4300_ = v___y_4348_;
v___y_4301_ = v___y_4344_;
v___y_4302_ = v___x_4369_;
v___y_4303_ = v___y_4349_;
v_fst_4304_ = v_val_4357_;
v_snd_4305_ = v_val_4362_;
v___y_4306_ = v___y_4350_;
v___y_4307_ = v___y_4346_;
v___y_4308_ = v___x_4385_;
goto v___jp_4291_;
}
}
}
}
}
}
}
}
v___jp_4390_:
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_box(0);
v_orderedAddInst_x3f_4343_ = v___x_4401_;
v___y_4344_ = v___y_4391_;
v___y_4345_ = v___y_4392_;
v___y_4346_ = v___y_4393_;
v___y_4347_ = v___y_4394_;
v___y_4348_ = v___y_4395_;
v___y_4349_ = v___y_4396_;
v___y_4350_ = v___y_4397_;
v___y_4351_ = v___y_4398_;
v___y_4352_ = v___y_4399_;
v___y_4353_ = v___y_4400_;
goto v___jp_4342_;
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4288_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4430_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4289_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4289_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4438_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4287_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4287_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
v___jp_3722_:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3731_, v___y_3730_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v_structs_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v_structs_3745_ = lean_ctor_get(v_a_3744_, 0);
lean_inc_ref(v_structs_3745_);
lean_dec(v_a_3744_);
v___x_3746_ = lean_array_get_size(v_structs_3745_);
lean_dec_ref(v_structs_3745_);
v___x_3747_ = lean_box(0);
lean_inc_ref(v___y_3740_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___y_3740_);
v___x_3749_ = v___x_3720_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___y_3740_);
v___x_3749_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; size_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___f_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_inc_ref(v___y_3738_);
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___y_3738_);
v___x_3751_ = lean_unsigned_to_nat(32u);
v___x_3752_ = lean_mk_empty_array_with_capacity(v___x_3751_);
v___x_3753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3754_ = ((size_t)5ULL);
lean_inc(v___y_3741_);
v___x_3755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3752_);
lean_ctor_set(v___x_3755_, 2, v___y_3741_);
lean_ctor_set(v___x_3755_, 3, v___y_3741_);
lean_ctor_set_usize(v___x_3755_, 4, v___x_3754_);
v___x_3756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3757_ = 0;
v___x_3758_ = lean_box(0);
lean_inc_ref_n(v___x_3755_, 7);
v___x_3759_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3746_);
lean_ctor_set(v___x_3759_, 1, v___x_3747_);
lean_ctor_set(v___x_3759_, 2, v_type_3699_);
lean_ctor_set(v___x_3759_, 3, v_val_3718_);
lean_ctor_set(v___x_3759_, 4, v___y_3723_);
lean_ctor_set(v___x_3759_, 5, v___y_3734_);
lean_ctor_set(v___x_3759_, 6, v___y_3724_);
lean_ctor_set(v___x_3759_, 7, v___y_3737_);
lean_ctor_set(v___x_3759_, 8, v___y_3728_);
lean_ctor_set(v___x_3759_, 9, v___y_3726_);
lean_ctor_set(v___x_3759_, 10, v___y_3729_);
lean_ctor_set(v___x_3759_, 11, v___y_3732_);
lean_ctor_set(v___x_3759_, 12, v___x_3747_);
lean_ctor_set(v___x_3759_, 13, v___x_3747_);
lean_ctor_set(v___x_3759_, 14, v___x_3747_);
lean_ctor_set(v___x_3759_, 15, v___x_3747_);
lean_ctor_set(v___x_3759_, 16, v___x_3747_);
lean_ctor_set(v___x_3759_, 17, v___y_3733_);
lean_ctor_set(v___x_3759_, 18, v___y_3736_);
lean_ctor_set(v___x_3759_, 19, v___x_3747_);
lean_ctor_set(v___x_3759_, 20, v___y_3725_);
lean_ctor_set(v___x_3759_, 21, v_a_3742_);
lean_ctor_set(v___x_3759_, 22, v___y_3739_);
lean_ctor_set(v___x_3759_, 23, v___y_3740_);
lean_ctor_set(v___x_3759_, 24, v___y_3738_);
lean_ctor_set(v___x_3759_, 25, v___x_3749_);
lean_ctor_set(v___x_3759_, 26, v___x_3750_);
lean_ctor_set(v___x_3759_, 27, v___x_3747_);
lean_ctor_set(v___x_3759_, 28, v___y_3735_);
lean_ctor_set(v___x_3759_, 29, v___y_3727_);
lean_ctor_set(v___x_3759_, 30, v___x_3755_);
lean_ctor_set(v___x_3759_, 31, v___x_3756_);
lean_ctor_set(v___x_3759_, 32, v___x_3755_);
lean_ctor_set(v___x_3759_, 33, v___x_3755_);
lean_ctor_set(v___x_3759_, 34, v___x_3755_);
lean_ctor_set(v___x_3759_, 35, v___x_3755_);
lean_ctor_set(v___x_3759_, 36, v___x_3747_);
lean_ctor_set(v___x_3759_, 37, v___x_3756_);
lean_ctor_set(v___x_3759_, 38, v___x_3755_);
lean_ctor_set(v___x_3759_, 39, v___x_3758_);
lean_ctor_set(v___x_3759_, 40, v___x_3755_);
lean_ctor_set(v___x_3759_, 41, v___x_3755_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*42, v___x_3757_);
v___f_3760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_3760_, 0, v___x_3759_);
v___x_3761_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3762_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3761_, v___f_3760_, v___y_3731_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3770_; 
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; 
v_unused_3771_ = lean_ctor_get(v___x_3762_, 0);
lean_dec(v_unused_3771_);
v___x_3764_ = v___x_3762_;
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3762_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3770_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3746_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3766_);
v___x_3768_ = v___x_3764_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_a_3772_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3762_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3762_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_a_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3781_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3743_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3743_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
v___jp_3789_:
{
if (lean_obj_tag(v___y_3791_) == 0)
{
lean_dec(v___y_3796_);
v___y_3723_ = v___y_3790_;
v___y_3724_ = v___y_3791_;
v___y_3725_ = v_a_3814_;
v___y_3726_ = v___y_3792_;
v___y_3727_ = v___y_3793_;
v___y_3728_ = v___y_3794_;
v___y_3729_ = v___y_3795_;
v___y_3730_ = v___y_3797_;
v___y_3731_ = v___y_3799_;
v___y_3732_ = v___y_3800_;
v___y_3733_ = v___y_3801_;
v___y_3734_ = v___y_3802_;
v___y_3735_ = v___y_3803_;
v___y_3736_ = v___y_3805_;
v___y_3737_ = v___y_3806_;
v___y_3738_ = v___y_3808_;
v___y_3739_ = v___y_3811_;
v___y_3740_ = v___y_3810_;
v___y_3741_ = v___y_3809_;
v_a_3742_ = v___y_3791_;
goto v___jp_3722_;
}
else
{
lean_object* v_val_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_val_3815_ = lean_ctor_get(v___y_3791_, 0);
v___x_3816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3817_ = l_Lean_mkConst(v___x_3816_, v___y_3796_);
lean_inc(v_val_3815_);
lean_inc_ref(v_type_3699_);
v___x_3818_ = l_Lean_mkAppB(v___x_3817_, v_type_3699_, v_val_3815_);
v___x_3819_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3818_, v___y_3812_, v___y_3798_, v___y_3804_, v___y_3813_, v___y_3797_, v___y_3807_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3820_);
v___y_3723_ = v___y_3790_;
v___y_3724_ = v___y_3791_;
v___y_3725_ = v_a_3814_;
v___y_3726_ = v___y_3792_;
v___y_3727_ = v___y_3793_;
v___y_3728_ = v___y_3794_;
v___y_3729_ = v___y_3795_;
v___y_3730_ = v___y_3797_;
v___y_3731_ = v___y_3799_;
v___y_3732_ = v___y_3800_;
v___y_3733_ = v___y_3801_;
v___y_3734_ = v___y_3802_;
v___y_3735_ = v___y_3803_;
v___y_3736_ = v___y_3805_;
v___y_3737_ = v___y_3806_;
v___y_3738_ = v___y_3808_;
v___y_3739_ = v___y_3811_;
v___y_3740_ = v___y_3810_;
v___y_3741_ = v___y_3809_;
v_a_3742_ = v___x_3821_;
goto v___jp_3722_;
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref_known(v___y_3791_, 1);
lean_dec(v_a_3814_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3790_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3822_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3819_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3819_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
v___jp_3830_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3835_);
v___x_3870_ = l_Lean_Name_mkStr2(v___y_3835_, v___x_3869_);
lean_inc(v___y_3839_);
v___x_3871_ = l_Lean_mkConst(v___x_3870_, v___y_3839_);
lean_inc_ref(v_type_3699_);
v___x_3872_ = l_Lean_mkAppB(v___x_3871_, v_type_3699_, v___y_3846_);
v___x_3873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3872_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3842_);
v___x_3876_ = l_Lean_Name_mkStr2(v___y_3842_, v___x_3875_);
lean_inc(v___y_3839_);
v___x_3877_ = l_Lean_mkConst(v___x_3876_, v___y_3839_);
lean_inc_ref(v_type_3699_);
v___x_3878_ = l_Lean_mkApp3(v___x_3877_, v_type_3699_, v___y_3856_, v___y_3834_);
v___x_3879_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3878_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3851_);
v___x_3882_ = l_Lean_Name_mkStr2(v___y_3851_, v___x_3881_);
lean_inc(v___y_3845_);
v___x_3883_ = l_Lean_mkConst(v___x_3882_, v___y_3845_);
lean_inc_ref_n(v_type_3699_, 3);
v___x_3884_ = l_Lean_mkApp4(v___x_3883_, v_type_3699_, v_type_3699_, v_type_3699_, v___y_3855_);
v___x_3885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3884_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3854_);
v___x_3888_ = l_Lean_Name_mkStr2(v___y_3854_, v___x_3887_);
v___x_3889_ = l_Lean_mkConst(v___x_3888_, v___y_3845_);
lean_inc_ref_n(v_type_3699_, 3);
v___x_3890_ = l_Lean_mkApp4(v___x_3889_, v_type_3699_, v_type_3699_, v_type_3699_, v___y_3858_);
v___x_3891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3890_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3832_);
v___x_3894_ = l_Lean_Name_mkStr2(v___y_3832_, v___x_3893_);
lean_inc(v___y_3839_);
v___x_3895_ = l_Lean_mkConst(v___x_3894_, v___y_3839_);
lean_inc_ref(v_type_3699_);
v___x_3896_ = l_Lean_mkAppB(v___x_3895_, v_type_3699_, v___y_3847_);
v___x_3897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3896_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3852_);
v___x_3900_ = l_Lean_Name_mkStr2(v___y_3852_, v___x_3899_);
v___x_3901_ = l_Lean_mkConst(v___x_3900_, v___y_3850_);
lean_inc_ref_n(v_type_3699_, 2);
lean_inc_ref(v___x_3901_);
v___x_3902_ = l_Lean_mkApp4(v___x_3901_, v___y_3837_, v_type_3699_, v_type_3699_, v___y_3836_);
v___x_3903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3902_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
lean_inc_ref_n(v_type_3699_, 2);
v___x_3905_ = l_Lean_mkApp4(v___x_3901_, v___y_3840_, v_type_3699_, v_type_3699_, v___y_3841_);
v___x_3906_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3905_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3906_) == 0)
{
if (lean_obj_tag(v___y_3849_) == 0)
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
v___y_3790_ = v___y_3843_;
v___y_3791_ = v___y_3831_;
v___y_3792_ = v___y_3833_;
v___y_3793_ = v_a_3898_;
v___y_3794_ = v___y_3844_;
v___y_3795_ = v___y_3838_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3867_;
v___y_3798_ = v___y_3864_;
v___y_3799_ = v___y_3859_;
v___y_3800_ = v___y_3848_;
v___y_3801_ = v_a_3874_;
v___y_3802_ = v___y_3849_;
v___y_3803_ = v_a_3892_;
v___y_3804_ = v___y_3865_;
v___y_3805_ = v_a_3880_;
v___y_3806_ = v___y_3853_;
v___y_3807_ = v___y_3868_;
v___y_3808_ = v_a_3907_;
v___y_3809_ = v___y_3857_;
v___y_3810_ = v_a_3904_;
v___y_3811_ = v_a_3886_;
v___y_3812_ = v___y_3863_;
v___y_3813_ = v___y_3866_;
v_a_3814_ = v___y_3849_;
goto v___jp_3789_;
}
else
{
lean_object* v_a_3908_; lean_object* v_val_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3908_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3906_, 1);
v_val_3909_ = lean_ctor_get(v___y_3849_, 0);
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3839_);
v___x_3911_ = l_Lean_mkConst(v___x_3910_, v___y_3839_);
lean_inc(v_val_3909_);
lean_inc_ref(v_type_3699_);
v___x_3912_ = l_Lean_mkAppB(v___x_3911_, v_type_3699_, v_val_3909_);
v___x_3913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3912_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v_a_3914_);
v___y_3790_ = v___y_3843_;
v___y_3791_ = v___y_3831_;
v___y_3792_ = v___y_3833_;
v___y_3793_ = v_a_3898_;
v___y_3794_ = v___y_3844_;
v___y_3795_ = v___y_3838_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3867_;
v___y_3798_ = v___y_3864_;
v___y_3799_ = v___y_3859_;
v___y_3800_ = v___y_3848_;
v___y_3801_ = v_a_3874_;
v___y_3802_ = v___y_3849_;
v___y_3803_ = v_a_3892_;
v___y_3804_ = v___y_3865_;
v___y_3805_ = v_a_3880_;
v___y_3806_ = v___y_3853_;
v___y_3807_ = v___y_3868_;
v___y_3808_ = v_a_3908_;
v___y_3809_ = v___y_3857_;
v___y_3810_ = v_a_3904_;
v___y_3811_ = v_a_3886_;
v___y_3812_ = v___y_3863_;
v___y_3813_ = v___y_3866_;
v_a_3814_ = v___x_3915_;
goto v___jp_3789_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_a_3908_);
lean_dec_ref_known(v___y_3849_, 1);
lean_dec(v_a_3904_);
lean_dec(v_a_3898_);
lean_dec(v_a_3892_);
lean_dec(v_a_3886_);
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3916_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3913_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3913_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_a_3904_);
lean_dec(v_a_3898_);
lean_dec(v_a_3892_);
lean_dec(v_a_3886_);
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3924_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3906_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3906_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v___x_3901_);
lean_dec(v_a_3898_);
lean_dec(v_a_3892_);
lean_dec(v_a_3886_);
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3932_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3903_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3903_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v_a_3892_);
lean_dec(v_a_3886_);
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3940_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3897_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3897_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec(v_a_3886_);
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3948_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3891_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3891_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_a_3880_);
lean_dec(v_a_3874_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3956_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3885_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3885_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_a_3874_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3964_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3879_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3879_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_3972_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3873_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3873_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
v___jp_3980_:
{
if (lean_obj_tag(v___y_3981_) == 1)
{
lean_object* v_val_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v_val_4019_ = lean_ctor_get(v___y_3981_, 0);
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_3989_);
v___x_4021_ = l_Lean_mkConst(v___x_4020_, v___y_3989_);
lean_inc_ref(v_type_3699_);
v___x_4022_ = l_Lean_Expr_app___override(v___x_4021_, v_type_3699_);
lean_inc(v_val_4019_);
v___x_4023_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4022_, v_val_4019_, v___y_4014_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_dec_ref_known(v___x_4023_, 1);
v___y_3831_ = v___y_3981_;
v___y_3832_ = v___y_3982_;
v___y_3833_ = v___y_3983_;
v___y_3834_ = v___y_3986_;
v___y_3835_ = v___y_3985_;
v___y_3836_ = v___y_3984_;
v___y_3837_ = v___y_3988_;
v___y_3838_ = v___y_3987_;
v___y_3839_ = v___y_3989_;
v___y_3840_ = v___y_3991_;
v___y_3841_ = v___y_3990_;
v___y_3842_ = v___y_3993_;
v___y_3843_ = v___y_3992_;
v___y_3844_ = v___y_3994_;
v___y_3845_ = v___y_3995_;
v___y_3846_ = v___y_3996_;
v___y_3847_ = v___y_3997_;
v___y_3848_ = v___y_3998_;
v___y_3849_ = v___y_3999_;
v___y_3850_ = v___y_4000_;
v___y_3851_ = v___y_4001_;
v___y_3852_ = v___y_4002_;
v___y_3853_ = v___y_4003_;
v___y_3854_ = v___y_4004_;
v___y_3855_ = v___y_4005_;
v___y_3856_ = v___y_4006_;
v___y_3857_ = v___y_4007_;
v___y_3858_ = v___y_4008_;
v___y_3859_ = v___y_4009_;
v___y_3860_ = v___y_4010_;
v___y_3861_ = v___y_4011_;
v___y_3862_ = v___y_4012_;
v___y_3863_ = v___y_4013_;
v___y_3864_ = v___y_4014_;
v___y_3865_ = v___y_4015_;
v___y_3866_ = v___y_4016_;
v___y_3867_ = v___y_4017_;
v___y_3868_ = v___y_4018_;
goto v___jp_3830_;
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref_known(v___y_3981_, 1);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4003_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
v___y_3831_ = v___y_3981_;
v___y_3832_ = v___y_3982_;
v___y_3833_ = v___y_3983_;
v___y_3834_ = v___y_3986_;
v___y_3835_ = v___y_3985_;
v___y_3836_ = v___y_3984_;
v___y_3837_ = v___y_3988_;
v___y_3838_ = v___y_3987_;
v___y_3839_ = v___y_3989_;
v___y_3840_ = v___y_3991_;
v___y_3841_ = v___y_3990_;
v___y_3842_ = v___y_3993_;
v___y_3843_ = v___y_3992_;
v___y_3844_ = v___y_3994_;
v___y_3845_ = v___y_3995_;
v___y_3846_ = v___y_3996_;
v___y_3847_ = v___y_3997_;
v___y_3848_ = v___y_3998_;
v___y_3849_ = v___y_3999_;
v___y_3850_ = v___y_4000_;
v___y_3851_ = v___y_4001_;
v___y_3852_ = v___y_4002_;
v___y_3853_ = v___y_4003_;
v___y_3854_ = v___y_4004_;
v___y_3855_ = v___y_4005_;
v___y_3856_ = v___y_4006_;
v___y_3857_ = v___y_4007_;
v___y_3858_ = v___y_4008_;
v___y_3859_ = v___y_4009_;
v___y_3860_ = v___y_4010_;
v___y_3861_ = v___y_4011_;
v___y_3862_ = v___y_4012_;
v___y_3863_ = v___y_4013_;
v___y_3864_ = v___y_4014_;
v___y_3865_ = v___y_4015_;
v___y_3866_ = v___y_4016_;
v___y_3867_ = v___y_4017_;
v___y_3868_ = v___y_4018_;
goto v___jp_3830_;
}
}
v___jp_4033_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4040_, 14);
v___x_4053_ = l_Lean_mkConst(v___x_4052_, v___y_4040_);
v___x_4054_ = l_Lean_mkAppB(v___x_4053_, v_base_3700_, v_natModuleInst_3701_);
v___x_4055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4056_ = l_Lean_mkConst(v___x_4055_, v___y_4040_);
lean_inc_ref_n(v___x_4054_, 4);
lean_inc_ref_n(v_type_3699_, 14);
v___x_4057_ = l_Lean_mkAppB(v___x_4056_, v_type_3699_, v___x_4054_);
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4059_ = l_Lean_mkConst(v___x_4058_, v___y_4040_);
lean_inc_ref_n(v___x_4057_, 2);
v___x_4060_ = l_Lean_mkAppB(v___x_4059_, v_type_3699_, v___x_4057_);
v___x_4061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4062_ = l_Lean_mkConst(v___x_4061_, v___y_4040_);
lean_inc_ref(v___x_4060_);
v___x_4063_ = l_Lean_mkAppB(v___x_4062_, v_type_3699_, v___x_4060_);
v___x_4064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4066_ = l_Lean_mkConst(v___x_4065_, v___y_4040_);
lean_inc_ref(v___x_4063_);
v___x_4067_ = l_Lean_mkAppB(v___x_4066_, v_type_3699_, v___x_4063_);
v___x_4068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4069_ = l_Lean_mkConst(v___x_4068_, v___y_4040_);
v___x_4070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4071_ = l_Lean_mkConst(v___x_4070_, v___y_4040_);
v___x_4072_ = l_Lean_mkAppB(v___x_4071_, v_type_3699_, v___x_4060_);
v___x_4073_ = l_Lean_mkAppB(v___x_4069_, v_type_3699_, v___x_4072_);
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4075_ = l_Lean_mkConst(v___x_4074_, v___y_4040_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4077_ = l_Lean_mkConst(v___x_4076_, v___y_4040_);
v___x_4078_ = l_Lean_mkAppB(v___x_4077_, v_type_3699_, v___x_4057_);
v___x_4079_ = l_Lean_mkAppB(v___x_4075_, v_type_3699_, v___x_4078_);
v___x_4080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4081_ = l_Lean_mkConst(v___x_4080_, v___y_4040_);
v___x_4082_ = l_Lean_mkAppB(v___x_4081_, v_type_3699_, v___x_4057_);
v___x_4083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___y_4040_);
v___x_4087_ = l_Lean_mkConst(v___x_4083_, v___x_4086_);
v___x_4088_ = l_Lean_Int_mkType;
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4090_ = l_Lean_mkConst(v___x_4089_, v___y_4040_);
v___x_4091_ = l_Lean_mkAppB(v___x_4090_, v_type_3699_, v___x_4054_);
lean_inc_ref(v___x_4087_);
v___x_4092_ = l_Lean_mkApp3(v___x_4087_, v___x_4088_, v_type_3699_, v___x_4091_);
v___x_4093_ = l_Lean_Nat_mkType;
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4095_ = l_Lean_mkConst(v___x_4094_, v___y_4040_);
v___x_4096_ = l_Lean_mkAppB(v___x_4095_, v_type_3699_, v___x_4054_);
v___x_4097_ = l_Lean_mkApp3(v___x_4087_, v___x_4093_, v_type_3699_, v___x_4096_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4099_ = l_Lean_mkConst(v___x_4098_, v___y_4040_);
v___x_4100_ = l_Lean_Expr_app___override(v___x_4099_, v_type_3699_);
v___x_4101_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4100_, v___x_4054_, v___y_4047_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
lean_dec_ref_known(v___x_4101_, 1);
v___x_4102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4040_);
v___x_4103_ = l_Lean_mkConst(v___x_4102_, v___y_4040_);
lean_inc_ref(v_type_3699_);
v___x_4104_ = l_Lean_Expr_app___override(v___x_4103_, v_type_3699_);
lean_inc_ref(v___x_4063_);
v___x_4105_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4104_, v___x_4063_, v___y_4047_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4105_, 1);
v___x_4106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4040_);
v___x_4108_ = l_Lean_mkConst(v___x_4107_, v___y_4040_);
v___x_4109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3699_);
v___x_4110_ = l_Lean_mkAppB(v___x_4108_, v_type_3699_, v___x_4109_);
lean_inc_ref(v___x_4067_);
v___x_4111_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4110_, v___x_4067_, v___y_4047_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec_ref_known(v___x_4111_, 1);
v___x_4112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4040_);
lean_inc_n(v_val_3718_, 2);
v___x_4114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_val_3718_);
lean_ctor_set(v___x_4114_, 1, v___y_4040_);
lean_inc_ref(v___x_4114_);
v___x_4115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_val_3718_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
lean_inc_ref(v___x_4115_);
v___x_4116_ = l_Lean_mkConst(v___x_4113_, v___x_4115_);
lean_inc_ref_n(v_type_3699_, 3);
v___x_4117_ = l_Lean_mkApp3(v___x_4116_, v_type_3699_, v_type_3699_, v_type_3699_);
lean_inc_ref(v___x_4073_);
v___x_4118_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4117_, v___x_4073_, v___y_4047_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec_ref_known(v___x_4118_, 1);
v___x_4119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4115_);
v___x_4121_ = l_Lean_mkConst(v___x_4120_, v___x_4115_);
lean_inc_ref_n(v_type_3699_, 3);
v___x_4122_ = l_Lean_mkApp3(v___x_4121_, v_type_3699_, v_type_3699_, v_type_3699_);
lean_inc_ref(v___x_4079_);
v___x_4123_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4122_, v___x_4079_, v___y_4047_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec_ref_known(v___x_4123_, 1);
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4040_);
v___x_4126_ = l_Lean_mkConst(v___x_4125_, v___y_4040_);
lean_inc_ref(v_type_3699_);
v___x_4127_ = l_Lean_Expr_app___override(v___x_4126_, v_type_3699_);
lean_inc_ref(v___x_4082_);
v___x_4128_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4127_, v___x_4082_, v___y_4047_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_dec_ref_known(v___x_4128_, 1);
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4085_);
lean_ctor_set(v___x_4131_, 1, v___x_4114_);
lean_inc_ref(v___x_4131_);
v___x_4132_ = l_Lean_mkConst(v___x_4130_, v___x_4131_);
lean_inc_ref_n(v_type_3699_, 2);
lean_inc_ref(v___x_4132_);
v___x_4133_ = l_Lean_mkApp3(v___x_4132_, v___x_4088_, v_type_3699_, v_type_3699_);
lean_inc_ref(v___x_4092_);
v___x_4134_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4133_, v___x_4092_, v___y_4047_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec_ref_known(v___x_4134_, 1);
lean_inc_ref_n(v_type_3699_, 2);
v___x_4135_ = l_Lean_mkApp3(v___x_4132_, v___x_4093_, v_type_3699_, v_type_3699_);
lean_inc_ref(v___x_4097_);
v___x_4136_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4135_, v___x_4097_, v___y_4047_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_dec_ref_known(v___x_4136_, 1);
if (lean_obj_tag(v___y_4034_) == 1)
{
lean_object* v_val_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_val_4137_ = lean_ctor_get(v___y_4034_, 0);
lean_inc(v___y_4040_);
v___x_4138_ = l_Lean_mkConst(v___x_4032_, v___y_4040_);
lean_inc_ref(v_type_3699_);
v___x_4139_ = l_Lean_Expr_app___override(v___x_4138_, v_type_3699_);
lean_inc(v_val_4137_);
v___x_4140_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4139_, v_val_4137_, v___y_4047_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref_known(v___x_4140_, 1);
v___y_3981_ = v___y_4035_;
v___y_3982_ = v___x_4124_;
v___y_3983_ = v___y_4036_;
v___y_3984_ = v___x_4092_;
v___y_3985_ = v___x_4064_;
v___y_3986_ = v___x_4067_;
v___y_3987_ = v___y_4039_;
v___y_3988_ = v___x_4088_;
v___y_3989_ = v___y_4040_;
v___y_3990_ = v___x_4097_;
v___y_3991_ = v___x_4093_;
v___y_3992_ = v___x_4054_;
v___y_3993_ = v___x_4106_;
v___y_3994_ = v___y_4037_;
v___y_3995_ = v___x_4115_;
v___y_3996_ = v___x_4063_;
v___y_3997_ = v___x_4082_;
v___y_3998_ = v_noNatDivInstQ_x3f_4041_;
v___y_3999_ = v___y_4034_;
v___y_4000_ = v___x_4131_;
v___y_4001_ = v___x_4112_;
v___y_4002_ = v___x_4129_;
v___y_4003_ = v___y_4038_;
v___y_4004_ = v___x_4119_;
v___y_4005_ = v___x_4073_;
v___y_4006_ = v___x_4109_;
v___y_4007_ = v___x_4084_;
v___y_4008_ = v___x_4079_;
v___y_4009_ = v___y_4042_;
v___y_4010_ = v___y_4043_;
v___y_4011_ = v___y_4044_;
v___y_4012_ = v___y_4045_;
v___y_4013_ = v___y_4046_;
v___y_4014_ = v___y_4047_;
v___y_4015_ = v___y_4048_;
v___y_4016_ = v___y_4049_;
v___y_4017_ = v___y_4050_;
v___y_4018_ = v___y_4051_;
goto v___jp_3980_;
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref_known(v___y_4034_, 1);
lean_dec_ref_known(v___x_4131_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
v___y_3981_ = v___y_4035_;
v___y_3982_ = v___x_4124_;
v___y_3983_ = v___y_4036_;
v___y_3984_ = v___x_4092_;
v___y_3985_ = v___x_4064_;
v___y_3986_ = v___x_4067_;
v___y_3987_ = v___y_4039_;
v___y_3988_ = v___x_4088_;
v___y_3989_ = v___y_4040_;
v___y_3990_ = v___x_4097_;
v___y_3991_ = v___x_4093_;
v___y_3992_ = v___x_4054_;
v___y_3993_ = v___x_4106_;
v___y_3994_ = v___y_4037_;
v___y_3995_ = v___x_4115_;
v___y_3996_ = v___x_4063_;
v___y_3997_ = v___x_4082_;
v___y_3998_ = v_noNatDivInstQ_x3f_4041_;
v___y_3999_ = v___y_4034_;
v___y_4000_ = v___x_4131_;
v___y_4001_ = v___x_4112_;
v___y_4002_ = v___x_4129_;
v___y_4003_ = v___y_4038_;
v___y_4004_ = v___x_4119_;
v___y_4005_ = v___x_4073_;
v___y_4006_ = v___x_4109_;
v___y_4007_ = v___x_4084_;
v___y_4008_ = v___x_4079_;
v___y_4009_ = v___y_4042_;
v___y_4010_ = v___y_4043_;
v___y_4011_ = v___y_4044_;
v___y_4012_ = v___y_4045_;
v___y_4013_ = v___y_4046_;
v___y_4014_ = v___y_4047_;
v___y_4015_ = v___y_4048_;
v___y_4016_ = v___y_4049_;
v___y_4017_ = v___y_4050_;
v___y_4018_ = v___y_4051_;
goto v___jp_3980_;
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref_known(v___x_4131_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4149_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4136_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4136_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref(v___x_4132_);
lean_dec_ref_known(v___x_4131_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4157_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4134_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4134_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref_known(v___x_4114_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4165_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4128_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4128_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref_known(v___x_4114_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4173_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4123_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4123_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref_known(v___x_4114_, 2);
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4181_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4118_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4118_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4189_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4111_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4111_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4197_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4105_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4105_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v___x_4097_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4082_);
lean_dec_ref(v___x_4079_);
lean_dec_ref(v___x_4073_);
lean_dec_ref(v___x_4067_);
lean_dec_ref(v___x_4063_);
lean_dec_ref(v___x_4054_);
lean_dec(v_noNatDivInstQ_x3f_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_type_3699_);
v_a_4205_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4101_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4101_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
v___jp_4213_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4231_ = lean_box(0);
lean_inc(v_val_3718_);
v___x_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_val_3718_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
lean_inc_ref(v___x_4232_);
v___x_4233_ = l_Lean_mkConst(v___x_4230_, v___x_4232_);
lean_inc_ref(v_base_3700_);
v___x_4234_ = l_Lean_Expr_app___override(v___x_4233_, v_base_3700_);
v___x_4235_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4234_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
if (lean_obj_tag(v_a_4236_) == 1)
{
lean_object* v_val_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v_val_4237_ = lean_ctor_get(v_a_4236_, 0);
lean_inc(v_val_4237_);
lean_dec_ref_known(v_a_4236_, 1);
v___x_4238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4232_);
v___x_4239_ = l_Lean_mkConst(v___x_4238_, v___x_4232_);
lean_inc_ref(v_base_3700_);
v___x_4240_ = l_Lean_mkAppB(v___x_4239_, v_base_3700_, v_val_4237_);
v___x_4241_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4240_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
if (lean_obj_tag(v_a_4242_) == 1)
{
lean_object* v_val_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v_val_4243_ = lean_ctor_get(v_a_4242_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v_a_4242_, 1);
v___x_4244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4232_);
v___x_4245_ = l_Lean_mkConst(v___x_4244_, v___x_4232_);
lean_inc_ref(v_natModuleInst_3701_);
lean_inc_ref(v_base_3700_);
v___x_4246_ = l_Lean_mkAppB(v___x_4245_, v_base_3700_, v_natModuleInst_3701_);
v___x_4247_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4246_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
if (lean_obj_tag(v_a_4248_) == 1)
{
lean_object* v_val_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4259_; 
v_val_4249_ = lean_ctor_get(v_a_4248_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_a_4248_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4251_ = v_a_4248_;
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_val_4249_);
lean_dec(v_a_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4259_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4232_);
v___x_4254_ = l_Lean_mkConst(v___x_4253_, v___x_4232_);
lean_inc_ref(v_natModuleInst_3701_);
lean_inc_ref(v_base_3700_);
v___x_4255_ = l_Lean_mkApp4(v___x_4254_, v_base_3700_, v_natModuleInst_3701_, v_val_4243_, v_val_4249_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4255_);
v___x_4257_ = v___x_4251_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
v___y_4034_ = v___y_4214_;
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v_isLinearInstQ_x3f_4219_;
v___y_4040_ = v___x_4232_;
v_noNatDivInstQ_x3f_4041_ = v___x_4257_;
v___y_4042_ = v___y_4220_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
goto v___jp_4033_;
}
}
}
else
{
lean_object* v___x_4260_; 
lean_dec(v_a_4248_);
lean_dec(v_val_4243_);
v___x_4260_ = lean_box(0);
v___y_4034_ = v___y_4214_;
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v_isLinearInstQ_x3f_4219_;
v___y_4040_ = v___x_4232_;
v_noNatDivInstQ_x3f_4041_ = v___x_4260_;
v___y_4042_ = v___y_4220_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
goto v___jp_4033_;
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v_val_4243_);
lean_dec_ref_known(v___x_4232_, 2);
lean_dec(v_isLinearInstQ_x3f_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4261_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4247_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4247_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_object* v___x_4269_; 
lean_dec(v_a_4242_);
v___x_4269_ = lean_box(0);
v___y_4034_ = v___y_4214_;
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v_isLinearInstQ_x3f_4219_;
v___y_4040_ = v___x_4232_;
v_noNatDivInstQ_x3f_4041_ = v___x_4269_;
v___y_4042_ = v___y_4220_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
goto v___jp_4033_;
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref_known(v___x_4232_, 2);
lean_dec(v_isLinearInstQ_x3f_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4270_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4241_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4241_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_a_4236_);
v___x_4278_ = lean_box(0);
v___y_4034_ = v___y_4214_;
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v_isLinearInstQ_x3f_4219_;
v___y_4040_ = v___x_4232_;
v_noNatDivInstQ_x3f_4041_ = v___x_4278_;
v___y_4042_ = v___y_4220_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
goto v___jp_4033_;
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec_ref_known(v___x_4232_, 2);
lean_dec(v_isLinearInstQ_x3f_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_del_object(v___x_3720_);
lean_dec(v_val_3718_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4279_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4235_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4235_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
lean_dec(v_a_3714_);
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v___x_4447_ = lean_box(0);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_4447_);
v___x_4449_ = v___x_3716_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
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
lean_dec_ref(v_natModuleInst_3701_);
lean_dec_ref(v_base_3700_);
lean_dec_ref(v_type_3699_);
v_a_4452_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_3713_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_3713_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4460_, lean_object* v_base_4461_, lean_object* v_natModuleInst_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4460_, v_base_4461_, v_natModuleInst_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec(v_a_4463_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; uint8_t v___x_4496_; 
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4495_ = lean_unsigned_to_nat(2u);
v___x_4496_ = l_Lean_Expr_isAppOfArity(v_type_4482_, v___x_4494_, v___x_4495_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; 
v___x_4497_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
return v___x_4497_;
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = l_Lean_Expr_appFn_x21(v_type_4482_);
v___x_4499_ = l_Lean_Expr_appArg_x21(v___x_4498_);
lean_dec_ref(v___x_4498_);
v___x_4500_ = l_Lean_Expr_appArg_x21(v_type_4482_);
v___x_4501_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4482_, v___x_4499_, v___x_4500_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec(v_a_4503_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4515_, lean_object* v_a_4516_, lean_object* v_s_4517_){
_start:
{
lean_object* v_structs_4518_; lean_object* v_typeIdOf_4519_; lean_object* v_exprToStructId_4520_; lean_object* v_exprToStructIdEntries_4521_; lean_object* v_forbiddenNatModules_4522_; lean_object* v_natStructs_4523_; lean_object* v_natTypeIdOf_4524_; lean_object* v_exprToNatStructId_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4533_; 
v_structs_4518_ = lean_ctor_get(v_s_4517_, 0);
v_typeIdOf_4519_ = lean_ctor_get(v_s_4517_, 1);
v_exprToStructId_4520_ = lean_ctor_get(v_s_4517_, 2);
v_exprToStructIdEntries_4521_ = lean_ctor_get(v_s_4517_, 3);
v_forbiddenNatModules_4522_ = lean_ctor_get(v_s_4517_, 4);
v_natStructs_4523_ = lean_ctor_get(v_s_4517_, 5);
v_natTypeIdOf_4524_ = lean_ctor_get(v_s_4517_, 6);
v_exprToNatStructId_4525_ = lean_ctor_get(v_s_4517_, 7);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_s_4517_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4527_ = v_s_4517_;
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_exprToNatStructId_4525_);
lean_inc(v_natTypeIdOf_4524_);
lean_inc(v_natStructs_4523_);
lean_inc(v_forbiddenNatModules_4522_);
lean_inc(v_exprToStructIdEntries_4521_);
lean_inc(v_exprToStructId_4520_);
lean_inc(v_typeIdOf_4519_);
lean_inc(v_structs_4518_);
lean_dec(v_s_4517_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4533_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4529_; lean_object* v___x_4531_; 
v___x_4529_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4519_, v_type_4515_, v_a_4516_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v___x_4529_);
v___x_4531_ = v___x_4527_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_structs_4518_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_exprToStructId_4520_);
lean_ctor_set(v_reuseFailAlloc_4532_, 3, v_exprToStructIdEntries_4521_);
lean_ctor_set(v_reuseFailAlloc_4532_, 4, v_forbiddenNatModules_4522_);
lean_ctor_set(v_reuseFailAlloc_4532_, 5, v_natStructs_4523_);
lean_ctor_set(v_reuseFailAlloc_4532_, 6, v_natTypeIdOf_4524_);
lean_ctor_set(v_reuseFailAlloc_4532_, 7, v_exprToNatStructId_4525_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4534_, lean_object* v_vals_4535_, lean_object* v_i_4536_, lean_object* v_k_4537_){
_start:
{
lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4538_ = lean_array_get_size(v_keys_4534_);
v___x_4539_ = lean_nat_dec_lt(v_i_4536_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
lean_dec(v_i_4536_);
v___x_4540_ = lean_box(0);
return v___x_4540_;
}
else
{
lean_object* v_k_x27_4541_; uint8_t v___x_4542_; 
v_k_x27_4541_ = lean_array_fget_borrowed(v_keys_4534_, v_i_4536_);
v___x_4542_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_4537_, v_k_x27_4541_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = lean_unsigned_to_nat(1u);
v___x_4544_ = lean_nat_add(v_i_4536_, v___x_4543_);
lean_dec(v_i_4536_);
v_i_4536_ = v___x_4544_;
goto _start;
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = lean_array_fget_borrowed(v_vals_4535_, v_i_4536_);
lean_dec(v_i_4536_);
lean_inc(v___x_4546_);
v___x_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4548_, lean_object* v_vals_4549_, lean_object* v_i_4550_, lean_object* v_k_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4548_, v_vals_4549_, v_i_4550_, v_k_4551_);
lean_dec_ref(v_k_4551_);
lean_dec_ref(v_vals_4549_);
lean_dec_ref(v_keys_4548_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4553_, size_t v_x_4554_, lean_object* v_x_4555_){
_start:
{
if (lean_obj_tag(v_x_4553_) == 0)
{
lean_object* v_es_4556_; lean_object* v___x_4557_; size_t v___x_4558_; size_t v___x_4559_; lean_object* v_j_4560_; lean_object* v___x_4561_; 
v_es_4556_ = lean_ctor_get(v_x_4553_, 0);
v___x_4557_ = lean_box(2);
v___x_4558_ = ((size_t)31ULL);
v___x_4559_ = lean_usize_land(v_x_4554_, v___x_4558_);
v_j_4560_ = lean_usize_to_nat(v___x_4559_);
v___x_4561_ = lean_array_get_borrowed(v___x_4557_, v_es_4556_, v_j_4560_);
lean_dec(v_j_4560_);
switch(lean_obj_tag(v___x_4561_))
{
case 0:
{
lean_object* v_key_4562_; lean_object* v_val_4563_; uint8_t v___x_4564_; 
v_key_4562_ = lean_ctor_get(v___x_4561_, 0);
v_val_4563_ = lean_ctor_get(v___x_4561_, 1);
v___x_4564_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4555_, v_key_4562_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_box(0);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; 
lean_inc(v_val_4563_);
v___x_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_val_4563_);
return v___x_4566_;
}
}
case 1:
{
lean_object* v_node_4567_; size_t v___x_4568_; size_t v___x_4569_; 
v_node_4567_ = lean_ctor_get(v___x_4561_, 0);
v___x_4568_ = ((size_t)5ULL);
v___x_4569_ = lean_usize_shift_right(v_x_4554_, v___x_4568_);
v_x_4553_ = v_node_4567_;
v_x_4554_ = v___x_4569_;
goto _start;
}
default: 
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_box(0);
return v___x_4571_;
}
}
}
else
{
lean_object* v_ks_4572_; lean_object* v_vs_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_ks_4572_ = lean_ctor_get(v_x_4553_, 0);
v_vs_4573_ = lean_ctor_get(v_x_4553_, 1);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4572_, v_vs_4573_, v___x_4574_, v_x_4555_);
return v___x_4575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4576_, lean_object* v_x_4577_, lean_object* v_x_4578_){
_start:
{
size_t v_x_8046__boxed_4579_; lean_object* v_res_4580_; 
v_x_8046__boxed_4579_ = lean_unbox_usize(v_x_4577_);
lean_dec(v_x_4577_);
v_res_4580_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4576_, v_x_8046__boxed_4579_, v_x_4578_);
lean_dec_ref(v_x_4578_);
lean_dec_ref(v_x_4576_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
uint64_t v___x_4583_; size_t v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4582_);
v___x_4584_ = lean_uint64_to_usize(v___x_4583_);
v___x_4585_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4581_, v___x_4584_, v_x_4582_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4586_, lean_object* v_x_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4586_, v_x_4587_);
lean_dec_ref(v_x_4587_);
lean_dec_ref(v_x_4586_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4592_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4671_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4604_ = v___x_4601_;
v_isShared_4605_ = v_isSharedCheck_4671_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4601_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4671_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
uint8_t v_linarith_4606_; 
v_linarith_4606_ = lean_ctor_get_uint8(v_a_4602_, sizeof(void*)*13 + 22);
lean_dec(v_a_4602_);
if (v_linarith_4606_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
lean_dec_ref(v_type_4589_);
v___x_4607_ = lean_box(0);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 0, v___x_4607_);
v___x_4609_ = v___x_4604_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
else
{
lean_object* v___x_4611_; 
lean_del_object(v___x_4604_);
lean_inc_ref(v_type_4589_);
v___x_4611_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4662_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4662_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4662_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_unbox(v_a_4612_);
lean_dec(v_a_4612_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_del_object(v___x_4614_);
v___x_4617_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4590_, v_a_4598_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4649_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4649_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4649_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_typeIdOf_4622_; lean_object* v___x_4623_; 
v_typeIdOf_4622_ = lean_ctor_get(v_a_4618_, 1);
lean_inc_ref(v_typeIdOf_4622_);
lean_dec(v_a_4618_);
v___x_4623_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4622_, v_type_4589_);
lean_dec_ref(v_typeIdOf_4622_);
if (lean_obj_tag(v___x_4623_) == 1)
{
lean_object* v_val_4624_; lean_object* v___x_4626_; 
lean_dec_ref(v_type_4589_);
v_val_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_val_4624_);
lean_dec_ref_known(v___x_4623_, 1);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v_val_4624_);
v___x_4626_ = v___x_4620_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_val_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
else
{
lean_object* v___x_4628_; 
lean_dec(v___x_4623_);
lean_del_object(v___x_4620_);
lean_inc_ref(v_type_4589_);
v___x_4628_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___f_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_n(v_a_4629_, 2);
lean_dec_ref_known(v___x_4628_, 1);
v___f_4630_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4630_, 0, v_type_4589_);
lean_closure_set(v___f_4630_, 1, v_a_4629_);
v___x_4631_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4632_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4631_, v___f_4630_, v_a_4590_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; 
v_unused_4640_ = lean_ctor_get(v___x_4632_, 0);
lean_dec(v_unused_4640_);
v___x_4634_ = v___x_4632_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_dec(v___x_4632_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 0, v_a_4629_);
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4629_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec(v_a_4629_);
v_a_4641_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4632_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4632_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
else
{
lean_dec_ref(v_type_4589_);
return v___x_4628_;
}
}
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec_ref(v_type_4589_);
v_a_4650_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4617_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4617_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
else
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
lean_dec_ref(v_type_4589_);
v___x_4658_ = lean_box(0);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4658_);
v___x_4660_ = v___x_4614_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec_ref(v_type_4589_);
v_a_4663_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4611_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4611_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_type_4589_);
v_a_4672_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4601_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4601_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec(v_a_4681_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4693_, lean_object* v_x_4694_, lean_object* v_x_4695_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4694_, v_x_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4697_, lean_object* v_x_4698_, lean_object* v_x_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4697_, v_x_4698_, v_x_4699_);
lean_dec_ref(v_x_4699_);
lean_dec_ref(v_x_4698_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4701_, lean_object* v_x_4702_, size_t v_x_4703_, lean_object* v_x_4704_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4702_, v_x_4703_, v_x_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4706_, lean_object* v_x_4707_, lean_object* v_x_4708_, lean_object* v_x_4709_){
_start:
{
size_t v_x_8272__boxed_4710_; lean_object* v_res_4711_; 
v_x_8272__boxed_4710_ = lean_unbox_usize(v_x_4708_);
lean_dec(v_x_4708_);
v_res_4711_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4706_, v_x_4707_, v_x_8272__boxed_4710_, v_x_4709_);
lean_dec_ref(v_x_4709_);
lean_dec_ref(v_x_4707_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4712_, lean_object* v_keys_4713_, lean_object* v_vals_4714_, lean_object* v_heq_4715_, lean_object* v_i_4716_, lean_object* v_k_4717_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4713_, v_vals_4714_, v_i_4716_, v_k_4717_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4719_, lean_object* v_keys_4720_, lean_object* v_vals_4721_, lean_object* v_heq_4722_, lean_object* v_i_4723_, lean_object* v_k_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4719_, v_keys_4720_, v_vals_4721_, v_heq_4722_, v_i_4723_, v_k_4724_);
lean_dec_ref(v_k_4724_);
lean_dec_ref(v_vals_4721_);
lean_dec_ref(v_keys_4720_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4726_, lean_object* v_type_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4735_ = lean_box(0);
v___x_4736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4736_, 0, v_u_4726_);
lean_ctor_set(v___x_4736_, 1, v___x_4735_);
v___x_4737_ = l_Lean_mkConst(v___x_4734_, v___x_4736_);
v___x_4738_ = l_Lean_Expr_app___override(v___x_4737_, v_type_4727_);
v___x_4739_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4738_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4740_, lean_object* v_type_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4740_, v_type_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
lean_dec(v_a_4746_);
lean_dec_ref(v_a_4745_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4749_, lean_object* v_type_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4749_, v_type_4750_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4763_, lean_object* v_type_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4763_, v_type_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec(v_a_4765_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4777_, lean_object* v_s_4778_){
_start:
{
lean_object* v_structs_4779_; lean_object* v_typeIdOf_4780_; lean_object* v_exprToStructId_4781_; lean_object* v_exprToStructIdEntries_4782_; lean_object* v_forbiddenNatModules_4783_; lean_object* v_natStructs_4784_; lean_object* v_natTypeIdOf_4785_; lean_object* v_exprToNatStructId_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4794_; 
v_structs_4779_ = lean_ctor_get(v_s_4778_, 0);
v_typeIdOf_4780_ = lean_ctor_get(v_s_4778_, 1);
v_exprToStructId_4781_ = lean_ctor_get(v_s_4778_, 2);
v_exprToStructIdEntries_4782_ = lean_ctor_get(v_s_4778_, 3);
v_forbiddenNatModules_4783_ = lean_ctor_get(v_s_4778_, 4);
v_natStructs_4784_ = lean_ctor_get(v_s_4778_, 5);
v_natTypeIdOf_4785_ = lean_ctor_get(v_s_4778_, 6);
v_exprToNatStructId_4786_ = lean_ctor_get(v_s_4778_, 7);
v_isSharedCheck_4794_ = !lean_is_exclusive(v_s_4778_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4788_ = v_s_4778_;
v_isShared_4789_ = v_isSharedCheck_4794_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_exprToNatStructId_4786_);
lean_inc(v_natTypeIdOf_4785_);
lean_inc(v_natStructs_4784_);
lean_inc(v_forbiddenNatModules_4783_);
lean_inc(v_exprToStructIdEntries_4782_);
lean_inc(v_exprToStructId_4781_);
lean_inc(v_typeIdOf_4780_);
lean_inc(v_structs_4779_);
lean_dec(v_s_4778_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4794_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4790_ = lean_array_push(v_natStructs_4784_, v___x_4777_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 5, v___x_4790_);
v___x_4792_ = v___x_4788_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_structs_4779_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v_typeIdOf_4780_);
lean_ctor_set(v_reuseFailAlloc_4793_, 2, v_exprToStructId_4781_);
lean_ctor_set(v_reuseFailAlloc_4793_, 3, v_exprToStructIdEntries_4782_);
lean_ctor_set(v_reuseFailAlloc_4793_, 4, v_forbiddenNatModules_4783_);
lean_ctor_set(v_reuseFailAlloc_4793_, 5, v___x_4790_);
lean_ctor_set(v_reuseFailAlloc_4793_, 6, v_natTypeIdOf_4785_);
lean_ctor_set(v_reuseFailAlloc_4793_, 7, v_exprToNatStructId_4786_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_ref_4801_; lean_object* v___x_4802_; lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4811_; 
v_ref_4801_ = lean_ctor_get(v___y_4798_, 5);
v___x_4802_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v___x_4809_; 
lean_inc(v_ref_4801_);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v_ref_4801_);
lean_ctor_set(v___x_4807_, 1, v_a_4803_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 1);
lean_ctor_set(v___x_4805_, 0, v___x_4807_);
v___x_4809_ = v___x_4805_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
return v_res_4818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4832_);
return v___x_4833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8(void){
_start:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7));
v___x_4836_ = l_Lean_stringToMessageData(v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; 
lean_inc_ref(v_type_4837_);
v___x_4849_ = l_Lean_Meta_getDecLevel(v_type_4837_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc_n(v_a_4850_, 2);
lean_dec_ref_known(v___x_4849_, 1);
lean_inc_ref(v_type_4837_);
v___x_4851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4850_, v_type_4837_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_5144_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_5144_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_5144_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
if (lean_obj_tag(v_a_4852_) == 1)
{
lean_object* v_val_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_del_object(v___x_4854_);
v_val_4856_ = lean_ctor_get(v_a_4852_, 0);
lean_inc_n(v_val_4856_, 2);
lean_dec_ref_known(v_a_4852_, 1);
v___x_4857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4858_ = lean_box(0);
lean_inc(v_a_4850_);
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v_a_4850_);
lean_ctor_set(v___x_4859_, 1, v___x_4858_);
lean_inc_ref(v___x_4859_);
v___x_4860_ = l_Lean_mkConst(v___x_4857_, v___x_4859_);
lean_inc_ref(v_type_4837_);
v___x_4861_ = l_Lean_mkAppB(v___x_4860_, v_type_4837_, v_val_4856_);
v___x_4862_ = l_Lean_Meta_Sym_canon(v___x_4861_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v___x_4864_ = l_Lean_Meta_Sym_shareCommon(v_a_4863_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc_n(v_a_4865_, 2);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4865_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
if (lean_obj_tag(v_a_4867_) == 1)
{
lean_object* v_val_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_5119_; 
v_val_4868_ = lean_ctor_get(v_a_4867_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v_a_4867_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_4870_ = v_a_4867_;
v_isShared_4871_ = v_isSharedCheck_5119_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_val_4868_);
lean_dec(v_a_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_5119_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4872_, v_a_4850_, v_type_4837_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4873_, 1);
v___x_4875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4875_, v_a_4850_, v_type_4837_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4878_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v___x_4876_, 1);
lean_inc(v_a_4874_);
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4878_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_4850_, v_type_4837_, v_a_4874_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4880_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4878_, 1);
lean_inc(v_a_4874_);
lean_inc(v_a_4877_);
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4880_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_4850_, v_type_4837_, v_a_4877_, v_a_4874_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref_known(v___x_4880_, 1);
lean_inc(v_a_4874_);
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4882_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_4850_, v_type_4837_, v_a_4874_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v___x_4882_, 1);
v___x_4884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4884_, v_a_4850_, v_type_4837_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc_n(v_a_4886_, 2);
lean_dec_ref_known(v___x_4885_, 1);
v___x_4887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4859_);
lean_inc_n(v_a_4850_, 2);
v___x_4888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4888_, 0, v_a_4850_);
lean_ctor_set(v___x_4888_, 1, v___x_4859_);
lean_inc_ref(v___x_4888_);
v___x_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_a_4850_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = l_Lean_mkConst(v___x_4887_, v___x_4889_);
lean_inc_ref_n(v_type_4837_, 3);
v___x_4891_ = l_Lean_mkApp4(v___x_4890_, v_type_4837_, v_type_4837_, v_type_4837_, v_a_4886_);
v___x_4892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4891_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v_orderedAddInst_x3f_4895_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
if (lean_obj_tag(v_a_4874_) == 1)
{
if (lean_obj_tag(v_a_4879_) == 1)
{
lean_object* v_val_5048_; lean_object* v_val_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_val_5048_ = lean_ctor_get(v_a_4874_, 0);
v_val_5049_ = lean_ctor_get(v_a_4879_, 0);
v___x_5050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4859_);
v___x_5051_ = l_Lean_mkConst(v___x_5050_, v___x_4859_);
lean_inc(v_val_5049_);
lean_inc(v_val_5048_);
lean_inc_ref(v_type_4837_);
v___x_5052_ = l_Lean_mkApp4(v___x_5051_, v_type_4837_, v_a_4886_, v_val_5048_, v_val_5049_);
v___x_5053_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5052_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_a_5054_);
lean_dec_ref_known(v___x_5053_, 1);
v_orderedAddInst_x3f_4895_ = v_a_5054_;
v___y_4896_ = v_a_4838_;
v___y_4897_ = v_a_4839_;
v___y_4898_ = v_a_4840_;
v___y_4899_ = v_a_4841_;
v___y_4900_ = v_a_4842_;
v___y_4901_ = v_a_4843_;
v___y_4902_ = v_a_4844_;
v___y_4903_ = v_a_4845_;
v___y_4904_ = v_a_4846_;
v___y_4905_ = v_a_4847_;
goto v___jp_4894_;
}
else
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5062_; 
lean_dec_ref_known(v_a_4879_, 1);
lean_dec_ref_known(v_a_4874_, 1);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4877_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5055_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5057_ = v___x_5053_;
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v___x_5053_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5060_; 
if (v_isShared_5058_ == 0)
{
v___x_5060_ = v___x_5057_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
}
else
{
lean_dec(v_a_4886_);
v___y_5037_ = v_a_4838_;
v___y_5038_ = v_a_4839_;
v___y_5039_ = v_a_4840_;
v___y_5040_ = v_a_4841_;
v___y_5041_ = v_a_4842_;
v___y_5042_ = v_a_4843_;
v___y_5043_ = v_a_4844_;
v___y_5044_ = v_a_4845_;
v___y_5045_ = v_a_4846_;
v___y_5046_ = v_a_4847_;
goto v___jp_5036_;
}
}
else
{
lean_dec(v_a_4886_);
v___y_5037_ = v_a_4838_;
v___y_5038_ = v_a_4839_;
v___y_5039_ = v_a_4840_;
v___y_5040_ = v_a_4841_;
v___y_5041_ = v_a_4842_;
v___y_5042_ = v_a_4843_;
v___y_5043_ = v_a_4844_;
v___y_5044_ = v_a_4845_;
v___y_5045_ = v_a_4846_;
v___y_5046_ = v_a_4847_;
goto v___jp_5036_;
}
v___jp_4894_:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4859_);
v___x_4907_ = l_Lean_mkConst(v___x_4906_, v___x_4859_);
lean_inc_ref(v_type_4837_);
v___x_4908_ = l_Lean_Expr_app___override(v___x_4907_, v_type_4837_);
v___x_4909_ = l_Lean_Meta_Sym_synthInstance(v___x_4908_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4909_, 1);
v___x_4911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4859_);
v___x_4912_ = l_Lean_mkConst(v___x_4911_, v___x_4859_);
lean_inc_ref(v_type_4837_);
v___x_4913_ = l_Lean_mkAppB(v___x_4912_, v_type_4837_, v_a_4910_);
v___x_4914_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4913_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4859_);
v___x_4917_ = l_Lean_mkConst(v___x_4916_, v___x_4859_);
lean_inc(v_val_4856_);
lean_inc_ref(v_type_4837_);
v___x_4918_ = l_Lean_mkAppB(v___x_4917_, v_type_4837_, v_val_4856_);
v___x_4919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4918_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4921_, v_a_4850_, v_type_4837_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4922_, 1);
v___x_4924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_4925_ = l_Lean_mkConst(v___x_4924_, v___x_4859_);
lean_inc_ref(v_type_4837_);
v___x_4926_ = l_Lean_mkAppB(v___x_4925_, v_type_4837_, v_a_4923_);
v___x_4927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4926_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4929_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___x_4927_, 1);
lean_inc_ref(v_type_4837_);
lean_inc(v_a_4850_);
v___x_4929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4850_, v_type_4837_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
lean_ctor_set(v___x_4933_, 1, v___x_4888_);
v___x_4934_ = l_Lean_mkConst(v___x_4931_, v___x_4933_);
v___x_4935_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4837_, 2);
v___x_4936_ = l_Lean_mkApp4(v___x_4934_, v___x_4935_, v_type_4837_, v_type_4837_, v_a_4930_);
v___x_4937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4936_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v_a_4938_; lean_object* v___x_4939_; 
v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___x_4937_, 1);
v___x_4939_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4896_, v___y_4904_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; lean_object* v_natStructs_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___f_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v___x_4939_, 1);
v_natStructs_4941_ = lean_ctor_get(v_a_4940_, 5);
lean_inc_ref(v_natStructs_4941_);
lean_dec(v_a_4940_);
v___x_4942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4850_);
v___x_4943_ = l_Lean_Level_succ___override(v_a_4850_);
v___x_4944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v___x_4858_);
v___x_4945_ = l_Lean_mkConst(v___x_4942_, v___x_4944_);
v___x_4946_ = l_Lean_Expr_app___override(v___x_4945_, v_a_4865_);
v___x_4947_ = lean_array_get_size(v_natStructs_4941_);
lean_dec_ref(v_natStructs_4941_);
v___x_4948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6);
v___x_4949_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v_val_4868_);
lean_ctor_set(v___x_4949_, 2, v_type_4837_);
lean_ctor_set(v___x_4949_, 3, v_a_4850_);
lean_ctor_set(v___x_4949_, 4, v_val_4856_);
lean_ctor_set(v___x_4949_, 5, v_a_4874_);
lean_ctor_set(v___x_4949_, 6, v_a_4877_);
lean_ctor_set(v___x_4949_, 7, v_a_4881_);
lean_ctor_set(v___x_4949_, 8, v_a_4879_);
lean_ctor_set(v___x_4949_, 9, v_orderedAddInst_x3f_4895_);
lean_ctor_set(v___x_4949_, 10, v_a_4883_);
lean_ctor_set(v___x_4949_, 11, v_a_4915_);
lean_ctor_set(v___x_4949_, 12, v___x_4946_);
lean_ctor_set(v___x_4949_, 13, v_a_4928_);
lean_ctor_set(v___x_4949_, 14, v_a_4920_);
lean_ctor_set(v___x_4949_, 15, v_a_4893_);
lean_ctor_set(v___x_4949_, 16, v_a_4938_);
lean_ctor_set(v___x_4949_, 17, v___x_4948_);
v___f_4950_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4950_, 0, v___x_4949_);
v___x_4951_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4952_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4951_, v___f_4950_, v___y_4896_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4962_; 
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4962_ == 0)
{
lean_object* v_unused_4963_; 
v_unused_4963_ = lean_ctor_get(v___x_4952_, 0);
lean_dec(v_unused_4963_);
v___x_4954_ = v___x_4952_;
v_isShared_4955_ = v_isSharedCheck_4962_;
goto v_resetjp_4953_;
}
else
{
lean_dec(v___x_4952_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4962_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4947_);
v___x_4957_ = v___x_4870_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4947_);
v___x_4957_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
lean_object* v___x_4959_; 
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 0, v___x_4957_);
v___x_4959_ = v___x_4954_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
lean_del_object(v___x_4870_);
v_a_4964_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4952_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4952_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_dec(v_a_4938_);
lean_dec(v_a_4928_);
lean_dec(v_a_4920_);
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_4972_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4939_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4939_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
else
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4987_; 
lean_dec(v_a_4928_);
lean_dec(v_a_4920_);
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_4980_ = lean_ctor_get(v___x_4937_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4937_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4937_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4937_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4983_ == 0)
{
v___x_4985_ = v___x_4982_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_dec(v_a_4928_);
lean_dec(v_a_4920_);
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_4988_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4929_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4929_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec(v_a_4920_);
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_4996_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4927_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4927_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec(v_a_4920_);
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5004_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4922_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4922_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec(v_a_4915_);
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5012_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4919_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4919_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5020_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_4914_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4914_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec(v_orderedAddInst_x3f_4895_);
lean_dec(v_a_4893_);
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5028_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_4909_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_4909_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
v___jp_5036_:
{
lean_object* v___x_5047_; 
v___x_5047_ = lean_box(0);
v_orderedAddInst_x3f_4895_ = v___x_5047_;
v___y_4896_ = v___y_5037_;
v___y_4897_ = v___y_5038_;
v___y_4898_ = v___y_5039_;
v___y_4899_ = v___y_5040_;
v___y_4900_ = v___y_5041_;
v___y_4901_ = v___y_5042_;
v___y_4902_ = v___y_5043_;
v___y_4903_ = v___y_5044_;
v___y_4904_ = v___y_5045_;
v___y_4905_ = v___y_5046_;
goto v___jp_4894_;
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5070_; 
lean_dec_ref_known(v___x_4888_, 2);
lean_dec(v_a_4886_);
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5063_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5065_ = v___x_4892_;
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_4892_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5070_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5066_ == 0)
{
v___x_5068_ = v___x_5065_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_5063_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec(v_a_4883_);
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5071_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_4885_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_4885_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v_a_4881_);
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5079_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_4882_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_4882_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_a_4879_);
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5087_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_4880_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_4880_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
lean_dec(v_a_4877_);
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5095_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_4878_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_4878_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec(v_a_4874_);
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5103_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_4876_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_4876_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_del_object(v___x_4870_);
lean_dec(v_val_4868_);
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5111_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_4873_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_4873_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
else
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
lean_dec(v_a_4867_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v___x_5120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8);
v___x_5121_ = l_Lean_indentExpr(v_a_4865_);
v___x_5122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5120_);
lean_ctor_set(v___x_5122_, 1, v___x_5121_);
v___x_5123_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5122_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
return v___x_5123_;
}
}
else
{
lean_dec(v_a_4865_);
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
return v___x_4866_;
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5124_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_4864_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_4864_);
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
lean_dec_ref_known(v___x_4859_, 2);
lean_dec(v_val_4856_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5132_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_4862_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_4862_);
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
lean_object* v___x_5140_; lean_object* v___x_5142_; 
lean_dec(v_a_4852_);
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v___x_5140_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_5140_);
v___x_5142_ = v___x_4854_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_a_4850_);
lean_dec_ref(v_type_4837_);
v_a_5145_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_4851_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_4851_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
lean_dec_ref(v_type_4837_);
v_a_5153_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_4849_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_4849_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
lean_dec(v_a_5169_);
lean_dec_ref(v_a_5168_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec(v_a_5162_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5174_, lean_object* v_msg_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5175_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5188_, lean_object* v_msg_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5188_, v_msg_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec(v___y_5190_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5202_, lean_object* v_a_5203_, lean_object* v_s_5204_){
_start:
{
lean_object* v_structs_5205_; lean_object* v_typeIdOf_5206_; lean_object* v_exprToStructId_5207_; lean_object* v_exprToStructIdEntries_5208_; lean_object* v_forbiddenNatModules_5209_; lean_object* v_natStructs_5210_; lean_object* v_natTypeIdOf_5211_; lean_object* v_exprToNatStructId_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5220_; 
v_structs_5205_ = lean_ctor_get(v_s_5204_, 0);
v_typeIdOf_5206_ = lean_ctor_get(v_s_5204_, 1);
v_exprToStructId_5207_ = lean_ctor_get(v_s_5204_, 2);
v_exprToStructIdEntries_5208_ = lean_ctor_get(v_s_5204_, 3);
v_forbiddenNatModules_5209_ = lean_ctor_get(v_s_5204_, 4);
v_natStructs_5210_ = lean_ctor_get(v_s_5204_, 5);
v_natTypeIdOf_5211_ = lean_ctor_get(v_s_5204_, 6);
v_exprToNatStructId_5212_ = lean_ctor_get(v_s_5204_, 7);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_s_5204_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5214_ = v_s_5204_;
v_isShared_5215_ = v_isSharedCheck_5220_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_exprToNatStructId_5212_);
lean_inc(v_natTypeIdOf_5211_);
lean_inc(v_natStructs_5210_);
lean_inc(v_forbiddenNatModules_5209_);
lean_inc(v_exprToStructIdEntries_5208_);
lean_inc(v_exprToStructId_5207_);
lean_inc(v_typeIdOf_5206_);
lean_inc(v_structs_5205_);
lean_dec(v_s_5204_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5220_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5216_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5211_, v_type_5202_, v_a_5203_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 6, v___x_5216_);
v___x_5218_ = v___x_5214_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_structs_5205_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v_typeIdOf_5206_);
lean_ctor_set(v_reuseFailAlloc_5219_, 2, v_exprToStructId_5207_);
lean_ctor_set(v_reuseFailAlloc_5219_, 3, v_exprToStructIdEntries_5208_);
lean_ctor_set(v_reuseFailAlloc_5219_, 4, v_forbiddenNatModules_5209_);
lean_ctor_set(v_reuseFailAlloc_5219_, 5, v_natStructs_5210_);
lean_ctor_set(v_reuseFailAlloc_5219_, 6, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5219_, 7, v_exprToNatStructId_5212_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5221_, lean_object* v_i_5222_, lean_object* v_k_5223_){
_start:
{
lean_object* v___x_5224_; uint8_t v___x_5225_; 
v___x_5224_ = lean_array_get_size(v_keys_5221_);
v___x_5225_ = lean_nat_dec_lt(v_i_5222_, v___x_5224_);
if (v___x_5225_ == 0)
{
lean_dec(v_i_5222_);
return v___x_5225_;
}
else
{
lean_object* v_k_x27_5226_; uint8_t v___x_5227_; 
v_k_x27_5226_ = lean_array_fget_borrowed(v_keys_5221_, v_i_5222_);
v___x_5227_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_5223_, v_k_x27_5226_);
if (v___x_5227_ == 0)
{
lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = lean_unsigned_to_nat(1u);
v___x_5229_ = lean_nat_add(v_i_5222_, v___x_5228_);
lean_dec(v_i_5222_);
v_i_5222_ = v___x_5229_;
goto _start;
}
else
{
lean_dec(v_i_5222_);
return v___x_5227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5231_, lean_object* v_i_5232_, lean_object* v_k_5233_){
_start:
{
uint8_t v_res_5234_; lean_object* v_r_5235_; 
v_res_5234_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5231_, v_i_5232_, v_k_5233_);
lean_dec_ref(v_k_5233_);
lean_dec_ref(v_keys_5231_);
v_r_5235_ = lean_box(v_res_5234_);
return v_r_5235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5236_, size_t v_x_5237_, lean_object* v_x_5238_){
_start:
{
if (lean_obj_tag(v_x_5236_) == 0)
{
lean_object* v_es_5239_; lean_object* v___x_5240_; size_t v___x_5241_; size_t v___x_5242_; lean_object* v_j_5243_; lean_object* v___x_5244_; 
v_es_5239_ = lean_ctor_get(v_x_5236_, 0);
v___x_5240_ = lean_box(2);
v___x_5241_ = ((size_t)31ULL);
v___x_5242_ = lean_usize_land(v_x_5237_, v___x_5241_);
v_j_5243_ = lean_usize_to_nat(v___x_5242_);
v___x_5244_ = lean_array_get_borrowed(v___x_5240_, v_es_5239_, v_j_5243_);
lean_dec(v_j_5243_);
switch(lean_obj_tag(v___x_5244_))
{
case 0:
{
lean_object* v_key_5245_; uint8_t v___x_5246_; 
v_key_5245_ = lean_ctor_get(v___x_5244_, 0);
v___x_5246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_5238_, v_key_5245_);
return v___x_5246_;
}
case 1:
{
lean_object* v_node_5247_; size_t v___x_5248_; size_t v___x_5249_; 
v_node_5247_ = lean_ctor_get(v___x_5244_, 0);
v___x_5248_ = ((size_t)5ULL);
v___x_5249_ = lean_usize_shift_right(v_x_5237_, v___x_5248_);
v_x_5236_ = v_node_5247_;
v_x_5237_ = v___x_5249_;
goto _start;
}
default: 
{
uint8_t v___x_5251_; 
v___x_5251_ = 0;
return v___x_5251_;
}
}
}
else
{
lean_object* v_ks_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; 
v_ks_5252_ = lean_ctor_get(v_x_5236_, 0);
v___x_5253_ = lean_unsigned_to_nat(0u);
v___x_5254_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5252_, v___x_5253_, v_x_5238_);
return v___x_5254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5255_, lean_object* v_x_5256_, lean_object* v_x_5257_){
_start:
{
size_t v_x_10639__boxed_5258_; uint8_t v_res_5259_; lean_object* v_r_5260_; 
v_x_10639__boxed_5258_ = lean_unbox_usize(v_x_5256_);
lean_dec(v_x_5256_);
v_res_5259_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5255_, v_x_10639__boxed_5258_, v_x_5257_);
lean_dec_ref(v_x_5257_);
lean_dec_ref(v_x_5255_);
v_r_5260_ = lean_box(v_res_5259_);
return v_r_5260_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5261_, lean_object* v_x_5262_){
_start:
{
uint64_t v___x_5263_; size_t v___x_5264_; uint8_t v___x_5265_; 
v___x_5263_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_5262_);
v___x_5264_ = lean_uint64_to_usize(v___x_5263_);
v___x_5265_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5261_, v___x_5264_, v_x_5262_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5266_, lean_object* v_x_5267_){
_start:
{
uint8_t v_res_5268_; lean_object* v_r_5269_; 
v_res_5268_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5266_, v_x_5267_);
lean_dec_ref(v_x_5267_);
lean_dec_ref(v_x_5266_);
v_r_5269_ = lean_box(v_res_5268_);
return v_r_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5273_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5372_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5285_ = v___x_5282_;
v_isShared_5286_ = v_isSharedCheck_5372_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5282_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5372_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
uint8_t v_linarith_5287_; 
v_linarith_5287_ = lean_ctor_get_uint8(v_a_5283_, sizeof(void*)*13 + 22);
lean_dec(v_a_5283_);
if (v_linarith_5287_ == 0)
{
lean_object* v___x_5288_; lean_object* v___x_5290_; 
lean_dec_ref(v_type_5270_);
v___x_5288_ = lean_box(0);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v___x_5288_);
v___x_5290_ = v___x_5285_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5288_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
else
{
lean_object* v___x_5292_; 
lean_del_object(v___x_5285_);
v___x_5292_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5271_, v_a_5279_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5363_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5295_ = v___x_5292_;
v_isShared_5296_ = v_isSharedCheck_5363_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5363_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v_forbiddenNatModules_5297_; uint8_t v___x_5298_; 
v_forbiddenNatModules_5297_ = lean_ctor_get(v_a_5293_, 4);
lean_inc_ref(v_forbiddenNatModules_5297_);
lean_dec(v_a_5293_);
v___x_5298_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5297_, v_type_5270_);
lean_dec_ref(v_forbiddenNatModules_5297_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; 
lean_del_object(v___x_5295_);
lean_inc_ref(v_type_5270_);
v___x_5299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5350_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5302_ = v___x_5299_;
v_isShared_5303_ = v_isSharedCheck_5350_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5350_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
uint8_t v___x_5304_; 
v___x_5304_ = lean_unbox(v_a_5300_);
lean_dec(v_a_5300_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_del_object(v___x_5302_);
v___x_5305_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5271_, v_a_5279_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5337_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5308_ = v___x_5305_;
v_isShared_5309_ = v_isSharedCheck_5337_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5337_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v_natTypeIdOf_5310_; lean_object* v___x_5311_; 
v_natTypeIdOf_5310_ = lean_ctor_get(v_a_5306_, 6);
lean_inc_ref(v_natTypeIdOf_5310_);
lean_dec(v_a_5306_);
v___x_5311_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5310_, v_type_5270_);
lean_dec_ref(v_natTypeIdOf_5310_);
if (lean_obj_tag(v___x_5311_) == 1)
{
lean_object* v_val_5312_; lean_object* v___x_5314_; 
lean_dec_ref(v_type_5270_);
v_val_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_val_5312_);
lean_dec_ref_known(v___x_5311_, 1);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v_val_5312_);
v___x_5314_ = v___x_5308_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_val_5312_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
else
{
lean_object* v___x_5316_; 
lean_dec(v___x_5311_);
lean_del_object(v___x_5308_);
lean_inc_ref(v_type_5270_);
v___x_5316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___f_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
lean_inc_n(v_a_5317_, 2);
lean_dec_ref_known(v___x_5316_, 1);
v___f_5318_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5318_, 0, v_type_5270_);
lean_closure_set(v___f_5318_, 1, v_a_5317_);
v___x_5319_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5320_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5319_, v___f_5318_, v_a_5271_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5327_ == 0)
{
lean_object* v_unused_5328_; 
v_unused_5328_ = lean_ctor_get(v___x_5320_, 0);
lean_dec(v_unused_5328_);
v___x_5322_ = v___x_5320_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_dec(v___x_5320_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set(v___x_5322_, 0, v_a_5317_);
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5317_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec(v_a_5317_);
v_a_5329_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5320_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5320_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
else
{
lean_dec_ref(v_type_5270_);
return v___x_5316_;
}
}
}
}
else
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
lean_dec_ref(v_type_5270_);
v_a_5338_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5305_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5305_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
else
{
lean_object* v___x_5346_; lean_object* v___x_5348_; 
lean_dec_ref(v_type_5270_);
v___x_5346_ = lean_box(0);
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5346_);
v___x_5348_ = v___x_5302_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
else
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_dec_ref(v_type_5270_);
v_a_5351_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5299_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5299_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
else
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
lean_dec_ref(v_type_5270_);
v___x_5359_ = lean_box(0);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5359_);
v___x_5361_ = v___x_5295_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
else
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
lean_dec_ref(v_type_5270_);
v_a_5364_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5366_ = v___x_5292_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5292_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec_ref(v_type_5270_);
v_a_5373_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5282_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5282_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec_ref(v_a_5386_);
lean_dec(v_a_5385_);
lean_dec_ref(v_a_5384_);
lean_dec(v_a_5383_);
lean_dec(v_a_5382_);
return v_res_5393_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5394_, lean_object* v_x_5395_, lean_object* v_x_5396_){
_start:
{
uint8_t v___x_5397_; 
v___x_5397_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5395_, v_x_5396_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5398_, lean_object* v_x_5399_, lean_object* v_x_5400_){
_start:
{
uint8_t v_res_5401_; lean_object* v_r_5402_; 
v_res_5401_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5398_, v_x_5399_, v_x_5400_);
lean_dec_ref(v_x_5400_);
lean_dec_ref(v_x_5399_);
v_r_5402_ = lean_box(v_res_5401_);
return v_r_5402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5403_, lean_object* v_x_5404_, size_t v_x_5405_, lean_object* v_x_5406_){
_start:
{
uint8_t v___x_5407_; 
v___x_5407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5404_, v_x_5405_, v_x_5406_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5408_, lean_object* v_x_5409_, lean_object* v_x_5410_, lean_object* v_x_5411_){
_start:
{
size_t v_x_10897__boxed_5412_; uint8_t v_res_5413_; lean_object* v_r_5414_; 
v_x_10897__boxed_5412_ = lean_unbox_usize(v_x_5410_);
lean_dec(v_x_5410_);
v_res_5413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5408_, v_x_5409_, v_x_10897__boxed_5412_, v_x_5411_);
lean_dec_ref(v_x_5411_);
lean_dec_ref(v_x_5409_);
v_r_5414_ = lean_box(v_res_5413_);
return v_r_5414_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5415_, lean_object* v_keys_5416_, lean_object* v_vals_5417_, lean_object* v_heq_5418_, lean_object* v_i_5419_, lean_object* v_k_5420_){
_start:
{
uint8_t v___x_5421_; 
v___x_5421_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5416_, v_i_5419_, v_k_5420_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5422_, lean_object* v_keys_5423_, lean_object* v_vals_5424_, lean_object* v_heq_5425_, lean_object* v_i_5426_, lean_object* v_k_5427_){
_start:
{
uint8_t v_res_5428_; lean_object* v_r_5429_; 
v_res_5428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5422_, v_keys_5423_, v_vals_5424_, v_heq_5425_, v_i_5426_, v_k_5427_);
lean_dec_ref(v_k_5427_);
lean_dec_ref(v_vals_5424_);
lean_dec_ref(v_keys_5423_);
v_r_5429_ = lean_box(v_res_5428_);
return v_r_5429_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
