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
lean_object* v_val_775_; lean_object* v_snd_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_val_775_ = lean_ctor_get(v_isCharInst_x3f_773_, 0);
v_snd_776_ = lean_ctor_get(v_val_775_, 1);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_dec_eq(v_snd_776_, v___x_777_);
if (v___x_778_ == 0)
{
uint8_t v___x_779_; 
v___x_779_ = 1;
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = 0;
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_781_);
lean_dec(v_isCharInst_x3f_781_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_787_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; uint8_t v_lia_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v_lia_802_ = lean_ctor_get_uint8(v_a_801_, sizeof(void*)*13 + 23);
lean_dec(v_a_801_);
if (v_lia_802_ == 0)
{
lean_dec_ref(v_type_784_);
goto v___jp_796_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
v___x_805_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_805_ == 0)
{
lean_dec_ref_known(v___x_803_, 1);
goto v___jp_796_;
}
else
{
return v___x_803_;
}
}
else
{
return v___x_803_;
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_type_784_);
v_a_806_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_800_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_800_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
v___jp_796_:
{
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = 0;
v___x_798_ = lean_box(v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec(v_a_815_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_827_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_866_; 
v_val_839_ = lean_ctor_get(v_ringId_x3f_827_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_ringId_x3f_827_);
if (v_isSharedCheck_866_ == 0)
{
v___x_841_ = v_ringId_x3f_827_;
v_isShared_842_ = v_isSharedCheck_866_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v_ringId_x3f_827_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_866_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_844_, 0, v_val_839_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_843_);
v___x_845_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_844_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_857_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_857_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_commRingInst_850_; lean_object* v___x_852_; 
v_commRingInst_850_ = lean_ctor_get(v_a_846_, 4);
lean_inc_ref(v_commRingInst_850_);
lean_dec(v_a_846_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_commRingInst_850_);
v___x_852_ = v___x_841_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_commRingInst_850_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_852_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_del_object(v___x_841_);
v_a_858_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_845_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_845_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v_ringId_x3f_827_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_896_, lean_object* v_type_897_, lean_object* v_commRingInst_x3f_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_898_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_918_; 
v_val_905_ = lean_ctor_get(v_commRingInst_x3f_898_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_commRingInst_x3f_898_);
if (v_isSharedCheck_918_ == 0)
{
v___x_907_ = v_commRingInst_x3f_898_;
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v_commRingInst_x3f_898_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_918_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v_u_896_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = l_Lean_mkConst(v___x_909_, v___x_911_);
v___x_913_ = l_Lean_mkAppB(v___x_912_, v_type_897_, v_val_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_913_);
v___x_915_ = v___x_907_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_commRingInst_x3f_898_);
v___x_919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_921_, 0, v_u_896_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_mkConst(v___x_919_, v___x_921_);
v___x_923_ = l_Lean_Expr_app___override(v___x_922_, v_type_897_);
v___x_924_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_923_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_925_, lean_object* v_type_926_, lean_object* v_commRingInst_x3f_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_925_, v_type_926_, v_commRingInst_x3f_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_935_, lean_object* v_type_936_, lean_object* v_commRingInst_x3f_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_935_, v_type_936_, v_commRingInst_x3f_937_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_950_, lean_object* v_type_951_, lean_object* v_commRingInst_x3f_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_950_, v_type_951_, v_commRingInst_x3f_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec(v_a_953_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_976_, lean_object* v_type_977_, lean_object* v_ringInst_x3f_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_978_) == 1)
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_998_; 
v_val_985_ = lean_ctor_get(v_ringInst_x3f_978_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_ringInst_x3f_978_);
if (v_isSharedCheck_998_ == 0)
{
v___x_987_ = v_ringInst_x3f_978_;
v_isShared_988_ = v_isSharedCheck_998_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v_ringInst_x3f_978_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_998_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v_u_976_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_mkConst(v___x_989_, v___x_991_);
v___x_993_ = l_Lean_mkAppB(v___x_992_, v_type_977_, v_val_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_993_);
v___x_995_ = v___x_987_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_ringInst_x3f_978_);
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_u_976_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_mkConst(v___x_999_, v___x_1001_);
v___x_1003_ = l_Lean_Expr_app___override(v___x_1002_, v_type_977_);
v___x_1004_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1003_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1005_, lean_object* v_type_1006_, lean_object* v_ringInst_x3f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1005_, v_type_1006_, v_ringInst_x3f_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1015_, lean_object* v_type_1016_, lean_object* v_ringInst_x3f_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1015_, v_type_1016_, v_ringInst_x3f_1017_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1030_, lean_object* v_type_1031_, lean_object* v_ringInst_x3f_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1030_, v_type_1031_, v_ringInst_x3f_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec(v_a_1033_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1056_, lean_object* v_type_1057_, lean_object* v_ringInst_x3f_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1058_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1078_; 
v_val_1065_ = lean_ctor_get(v_ringInst_x3f_1058_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_ringInst_x3f_1058_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1067_ = v_ringInst_x3f_1058_;
v_isShared_1068_ = v_isSharedCheck_1078_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v_ringInst_x3f_1058_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1078_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_u_1056_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_mkConst(v___x_1069_, v___x_1071_);
v___x_1073_ = l_Lean_mkAppB(v___x_1072_, v_type_1057_, v_val_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1073_);
v___x_1075_ = v___x_1067_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_ringInst_x3f_1058_);
v___x_1079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_u_1056_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_mkConst(v___x_1079_, v___x_1081_);
v___x_1083_ = l_Lean_Expr_app___override(v___x_1082_, v_type_1057_);
v___x_1084_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1083_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1085_, lean_object* v_type_1086_, lean_object* v_ringInst_x3f_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1085_, v_type_1086_, v_ringInst_x3f_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1095_, lean_object* v_type_1096_, lean_object* v_ringInst_x3f_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1095_, v_type_1096_, v_ringInst_x3f_1097_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1110_, lean_object* v_type_1111_, lean_object* v_ringInst_x3f_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1110_, v_type_1111_, v_ringInst_x3f_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1132_, lean_object* v_type_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1146_ = lean_box(0);
v___x_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_u_1132_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
lean_inc_ref(v___x_1147_);
v___x_1148_ = l_Lean_mkConst(v___x_1145_, v___x_1147_);
lean_inc_ref(v_type_1133_);
v___x_1149_ = l_Lean_Expr_app___override(v___x_1148_, v_type_1133_);
v___x_1150_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1149_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1232_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1232_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1232_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
if (lean_obj_tag(v_a_1151_) == 1)
{
lean_object* v_val_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1153_);
v_val_1155_ = lean_ctor_get(v_a_1151_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1151_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1157_ = v_a_1151_;
v_isShared_1158_ = v_isSharedCheck_1227_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_val_1155_);
lean_dec(v_a_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1227_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1160_ = l_Lean_mkConst(v___x_1159_, v___x_1147_);
lean_inc_ref(v_type_1133_);
v___x_1161_ = l_Lean_mkAppB(v___x_1160_, v_type_1133_, v_val_1155_);
v___x_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1161_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1218_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1218_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1218_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = l_Lean_Meta_mkNumeral(v_type_1133_, v___x_1174_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_n(v_a_1176_, 2);
lean_dec_ref_known(v___x_1175_, 1);
lean_inc(v_a_1163_);
v___x_1177_ = l_Lean_Meta_isDefEqD(v_a_1163_, v_a_1176_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___x_1179_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v_a_1181_; lean_object* v___x_1182_; 
lean_inc(v_a_1163_);
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1163_, v_a_1176_);
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1138_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; uint8_t v_verbose_1184_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_verbose_1184_ = lean_ctor_get_uint8(v_a_1183_, 0);
lean_dec(v_a_1183_);
if (v_verbose_1184_ == 0)
{
lean_dec(v_a_1181_);
goto v___jp_1167_;
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Meta_Sym_reportIssue(v_a_1181_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_dec_ref_known(v___x_1185_, 1);
goto v___jp_1167_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
lean_del_object(v___x_1157_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_a_1181_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
lean_del_object(v___x_1157_);
v_a_1194_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1182_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1182_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_dec(v_a_1176_);
goto v___jp_1167_;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_a_1176_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
lean_del_object(v___x_1157_);
v_a_1202_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1177_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1177_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
lean_del_object(v___x_1157_);
v_a_1210_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1175_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1175_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
v___jp_1167_:
{
lean_object* v___x_1169_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_a_1163_);
v___x_1169_ = v___x_1157_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1163_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1169_);
v___x_1171_ = v___x_1165_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
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
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1157_);
lean_dec_ref(v_type_1133_);
v_a_1219_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1162_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1162_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_a_1151_);
lean_dec_ref_known(v___x_1147_, 2);
lean_dec_ref(v_type_1133_);
v___x_1228_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1228_);
v___x_1230_ = v___x_1153_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1147_, 2);
lean_dec_ref(v_type_1133_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1233_, lean_object* v_type_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1233_, v_type_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
return v_res_1246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1254_ = l_Lean_stringToMessageData(v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1255_, lean_object* v_type_1256_, lean_object* v_semiringInst_x3f_1257_, lean_object* v_leInst_x3f_1258_, lean_object* v_ltInst_x3f_1259_, lean_object* v_preorderInst_x3f_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1257_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1258_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1259_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1260_) == 1)
{
lean_object* v_val_1271_; lean_object* v_val_1272_; lean_object* v_val_1273_; lean_object* v_val_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_isOrdType_1279_; lean_object* v___x_1280_; 
v_val_1271_ = lean_ctor_get(v_semiringInst_x3f_1257_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_semiringInst_x3f_1257_, 1);
v_val_1272_ = lean_ctor_get(v_leInst_x3f_1258_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v_leInst_x3f_1258_, 1);
v_val_1273_ = lean_ctor_get(v_ltInst_x3f_1259_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v_ltInst_x3f_1259_, 1);
v_val_1274_ = lean_ctor_get(v_preorderInst_x3f_1260_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_preorderInst_x3f_1260_, 1);
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_u_1255_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Lean_mkConst(v___x_1275_, v___x_1277_);
v_isOrdType_1279_ = l_Lean_mkApp5(v___x_1278_, v_type_1256_, v_val_1271_, v_val_1272_, v_val_1273_, v_val_1274_);
lean_inc_ref(v_isOrdType_1279_);
v___x_1280_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1279_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
if (lean_obj_tag(v_a_1281_) == 1)
{
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_isOrdType_1279_);
return v___x_1280_;
}
else
{
lean_object* v___x_1282_; 
lean_dec(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1261_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; uint8_t v_verbose_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_verbose_1284_ = lean_ctor_get_uint8(v_a_1283_, 0);
lean_dec(v_a_1283_);
if (v_verbose_1284_ == 0)
{
lean_dec_ref(v_isOrdType_1279_);
goto v___jp_1268_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1286_ = l_Lean_indentExpr(v_isOrdType_1279_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Meta_Sym_reportIssue(v___x_1287_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_dec_ref_known(v___x_1288_, 1);
goto v___jp_1268_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_isOrdType_1279_);
v_a_1297_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1282_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1282_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1279_);
return v___x_1280_;
}
}
else
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref_known(v_leInst_x3f_1258_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1257_, 1);
lean_dec(v_preorderInst_x3f_1260_);
lean_dec_ref(v_type_1256_);
lean_dec(v_u_1255_);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_ltInst_x3f_1259_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v_ltInst_x3f_1259_, 0);
lean_dec(v_unused_1313_);
v___x_1306_ = v_ltInst_x3f_1259_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v_ltInst_x3f_1259_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_box(0);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref_known(v_semiringInst_x3f_1257_, 1);
lean_dec(v_preorderInst_x3f_1260_);
lean_dec(v_ltInst_x3f_1259_);
lean_dec_ref(v_type_1256_);
lean_dec(v_u_1255_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_leInst_x3f_1258_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_leInst_x3f_1258_, 0);
lean_dec(v_unused_1322_);
v___x_1315_ = v_leInst_x3f_1258_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v_leInst_x3f_1258_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(0);
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_preorderInst_x3f_1260_);
lean_dec(v_ltInst_x3f_1259_);
lean_dec(v_leInst_x3f_1258_);
lean_dec_ref(v_type_1256_);
lean_dec(v_u_1255_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_semiringInst_x3f_1257_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v_semiringInst_x3f_1257_, 0);
lean_dec(v_unused_1331_);
v___x_1324_ = v_semiringInst_x3f_1257_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_semiringInst_x3f_1257_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_box(0);
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_preorderInst_x3f_1260_);
lean_dec(v_ltInst_x3f_1259_);
lean_dec(v_leInst_x3f_1258_);
lean_dec(v_semiringInst_x3f_1257_);
lean_dec_ref(v_type_1256_);
lean_dec(v_u_1255_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
v___jp_1268_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1334_, lean_object* v_type_1335_, lean_object* v_semiringInst_x3f_1336_, lean_object* v_leInst_x3f_1337_, lean_object* v_ltInst_x3f_1338_, lean_object* v_preorderInst_x3f_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1334_, v_type_1335_, v_semiringInst_x3f_1336_, v_leInst_x3f_1337_, v_ltInst_x3f_1338_, v_preorderInst_x3f_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1348_, lean_object* v_type_1349_, lean_object* v_semiringInst_x3f_1350_, lean_object* v_leInst_x3f_1351_, lean_object* v_ltInst_x3f_1352_, lean_object* v_preorderInst_x3f_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1348_, v_type_1349_, v_semiringInst_x3f_1350_, v_leInst_x3f_1351_, v_ltInst_x3f_1352_, v_preorderInst_x3f_1353_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1366_ = _args[0];
lean_object* v_type_1367_ = _args[1];
lean_object* v_semiringInst_x3f_1368_ = _args[2];
lean_object* v_leInst_x3f_1369_ = _args[3];
lean_object* v_ltInst_x3f_1370_ = _args[4];
lean_object* v_preorderInst_x3f_1371_ = _args[5];
lean_object* v_a_1372_ = _args[6];
lean_object* v_a_1373_ = _args[7];
lean_object* v_a_1374_ = _args[8];
lean_object* v_a_1375_ = _args[9];
lean_object* v_a_1376_ = _args[10];
lean_object* v_a_1377_ = _args[11];
lean_object* v_a_1378_ = _args[12];
lean_object* v_a_1379_ = _args[13];
lean_object* v_a_1380_ = _args[14];
lean_object* v_a_1381_ = _args[15];
lean_object* v_a_1382_ = _args[16];
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1366_, v_type_1367_, v_semiringInst_x3f_1368_, v_leInst_x3f_1369_, v_ltInst_x3f_1370_, v_preorderInst_x3f_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec(v_a_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1394_, lean_object* v_type_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_natModuleType_1406_; lean_object* v___x_1407_; 
v___x_1402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_u_1394_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
lean_inc_ref(v___x_1404_);
v___x_1405_ = l_Lean_mkConst(v___x_1402_, v___x_1404_);
lean_inc_ref(v_type_1395_);
v_natModuleType_1406_ = l_Lean_Expr_app___override(v___x_1405_, v_type_1395_);
v___x_1407_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1406_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
if (lean_obj_tag(v_a_1408_) == 1)
{
lean_object* v_val_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_del_object(v___x_1410_);
v_val_1412_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v_a_1408_, 1);
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1414_ = l_Lean_mkConst(v___x_1413_, v___x_1404_);
v___x_1415_ = l_Lean_mkAppB(v___x_1414_, v_type_1395_, v_val_1412_);
v___x_1416_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1415_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec(v_a_1408_);
lean_dec_ref_known(v___x_1404_, 2);
lean_dec_ref(v_type_1395_);
v___x_1417_ = lean_box(0);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1417_);
v___x_1419_ = v___x_1410_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1404_, 2);
lean_dec_ref(v_type_1395_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1422_, lean_object* v_type_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1422_, v_type_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1431_, lean_object* v_type_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1431_, v_type_1432_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1445_, lean_object* v_type_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1445_, v_type_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec(v_a_1447_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1459_, lean_object* v_u_1460_, lean_object* v_type_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_u_1460_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_mkConst(v_declName_1459_, v___x_1469_);
v___x_1471_ = l_Lean_Expr_app___override(v___x_1470_, v_type_1461_);
v___x_1472_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1471_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1473_, lean_object* v_u_1474_, lean_object* v_type_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1473_, v_u_1474_, v_type_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1483_, lean_object* v_u_1484_, lean_object* v_type_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1483_, v_u_1484_, v_type_1485_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1498_, lean_object* v_u_1499_, lean_object* v_type_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1498_, v_u_1499_, v_type_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec(v_a_1501_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1513_, lean_object* v_u_1514_, lean_object* v_type_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_u_1514_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_mkConst(v_declName_1513_, v___x_1524_);
v___x_1526_ = l_Lean_Expr_app___override(v___x_1525_, v_type_1515_);
v___x_1527_ = l_Lean_Meta_Sym_synthInstance(v___x_1526_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1528_, lean_object* v_u_1529_, lean_object* v_type_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1528_, v_u_1529_, v_type_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1539_, lean_object* v_u_1540_, lean_object* v_type_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1539_, v_u_1540_, v_type_1541_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1554_, lean_object* v_u_1555_, lean_object* v_type_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1554_, v_u_1555_, v_type_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec(v_a_1557_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1569_, lean_object* v_u_1570_, lean_object* v_type_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1579_ = lean_box(0);
lean_inc_n(v_u_1570_, 2);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_u_1570_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_u_1570_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_u_1570_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_mkConst(v_declName_1569_, v___x_1582_);
lean_inc_ref_n(v_type_1571_, 2);
v___x_1584_ = l_Lean_mkApp3(v___x_1583_, v_type_1571_, v_type_1571_, v_type_1571_);
v___x_1585_ = l_Lean_Meta_Sym_synthInstance(v___x_1584_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1586_, lean_object* v_u_1587_, lean_object* v_type_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1586_, v_u_1587_, v_type_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1597_, lean_object* v_u_1598_, lean_object* v_type_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1597_, v_u_1598_, v_type_1599_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1612_, lean_object* v_u_1613_, lean_object* v_type_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1612_, v_u_1613_, v_type_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
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
return v_res_1626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = l_Lean_Level_ofNat(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1632_, lean_object* v_type_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1643_ = lean_box(0);
lean_inc(v_u_1632_);
v___x_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_u_1632_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_u_1632_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1642_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_mkConst(v___x_1641_, v___x_1646_);
v___x_1648_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1633_);
v___x_1649_ = l_Lean_mkApp3(v___x_1647_, v___x_1648_, v_type_1633_, v_type_1633_);
v___x_1650_ = l_Lean_Meta_Sym_synthInstance(v___x_1649_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1651_, lean_object* v_type_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1651_, v_type_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1661_, lean_object* v_type_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1661_, v_type_1662_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1675_, lean_object* v_type_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1675_, v_type_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec(v_a_1677_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1689_, lean_object* v_type_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1700_ = lean_box(0);
lean_inc(v_u_1689_);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_u_1689_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_u_1689_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1699_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l_Lean_mkConst(v___x_1698_, v___x_1703_);
v___x_1705_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1690_);
v___x_1706_ = l_Lean_mkApp3(v___x_1704_, v___x_1705_, v_type_1690_, v_type_1690_);
v___x_1707_ = l_Lean_Meta_Sym_synthInstance(v___x_1706_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1708_, lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1708_, v_type_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1718_, lean_object* v_type_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1718_, v_type_1719_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1732_, lean_object* v_type_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1732_, v_type_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec(v_a_1734_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1746_, lean_object* v_parentInst_x3f_1747_, lean_object* v_childInst_x3f_1748_, lean_object* v_toFieldName_1749_, lean_object* v_u_1750_, lean_object* v_type_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1746_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1747_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1748_) == 1)
{
lean_object* v_val_1762_; lean_object* v_val_1763_; lean_object* v_val_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_toField_1768_; lean_object* v___x_1769_; 
v_val_1762_ = lean_ctor_get(v_leInst_x3f_1746_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v_leInst_x3f_1746_, 1);
v_val_1763_ = lean_ctor_get(v_parentInst_x3f_1747_, 0);
lean_inc_n(v_val_1763_, 2);
lean_dec_ref_known(v_parentInst_x3f_1747_, 1);
v_val_1764_ = lean_ctor_get(v_childInst_x3f_1748_, 0);
v___x_1765_ = lean_box(0);
v___x_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_u_1750_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_mkConst(v_toFieldName_1749_, v___x_1766_);
lean_inc(v_val_1764_);
v_toField_1768_ = l_Lean_mkApp3(v___x_1767_, v_type_1751_, v_val_1762_, v_val_1764_);
lean_inc_ref(v_toField_1768_);
v___x_1769_ = l_Lean_Meta_isDefEqD(v_val_1763_, v_toField_1768_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1800_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1800_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1800_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_unbox(v_a_1770_);
lean_dec(v_a_1770_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v_a_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1772_);
lean_dec_ref_known(v_childInst_x3f_1748_, 1);
v___x_1775_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1763_, v_toField_1768_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1752_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; uint8_t v_verbose_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v_verbose_1779_ = lean_ctor_get_uint8(v_a_1778_, 0);
lean_dec(v_a_1778_);
if (v_verbose_1779_ == 0)
{
lean_dec(v_a_1776_);
goto v___jp_1759_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Meta_Sym_reportIssue(v_a_1776_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_dec_ref_known(v___x_1780_, 1);
goto v___jp_1759_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_a_1776_);
v_a_1789_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1777_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1777_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v_toField_1768_);
lean_dec(v_val_1763_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_childInst_x3f_1748_);
v___x_1798_ = v___x_1772_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_childInst_x3f_1748_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_toField_1768_);
lean_dec(v_val_1763_);
lean_dec_ref_known(v_childInst_x3f_1748_, 1);
v_a_1801_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1769_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1769_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref_known(v_leInst_x3f_1746_, 1);
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_parentInst_x3f_1747_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v_parentInst_x3f_1747_, 0);
lean_dec(v_unused_1817_);
v___x_1810_ = v_parentInst_x3f_1747_;
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v_parentInst_x3f_1747_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
lean_dec(v_parentInst_x3f_1747_);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_leInst_x3f_1746_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_leInst_x3f_1746_, 0);
lean_dec(v_unused_1826_);
v___x_1819_ = v_leInst_x3f_1746_;
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v_leInst_x3f_1746_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1821_);
v___x_1823_ = v___x_1819_;
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
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
lean_dec(v_parentInst_x3f_1747_);
lean_dec(v_leInst_x3f_1746_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
v___jp_1759_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1829_, lean_object* v_parentInst_x3f_1830_, lean_object* v_childInst_x3f_1831_, lean_object* v_toFieldName_1832_, lean_object* v_u_1833_, lean_object* v_type_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1829_, v_parentInst_x3f_1830_, v_childInst_x3f_1831_, v_toFieldName_1832_, v_u_1833_, v_type_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1843_, lean_object* v_parentInst_x3f_1844_, lean_object* v_childInst_x3f_1845_, lean_object* v_toFieldName_1846_, lean_object* v_u_1847_, lean_object* v_type_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1843_, v_parentInst_x3f_1844_, v_childInst_x3f_1845_, v_toFieldName_1846_, v_u_1847_, v_type_1848_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1861_ = _args[0];
lean_object* v_parentInst_x3f_1862_ = _args[1];
lean_object* v_childInst_x3f_1863_ = _args[2];
lean_object* v_toFieldName_1864_ = _args[3];
lean_object* v_u_1865_ = _args[4];
lean_object* v_type_1866_ = _args[5];
lean_object* v_a_1867_ = _args[6];
lean_object* v_a_1868_ = _args[7];
lean_object* v_a_1869_ = _args[8];
lean_object* v_a_1870_ = _args[9];
lean_object* v_a_1871_ = _args[10];
lean_object* v_a_1872_ = _args[11];
lean_object* v_a_1873_ = _args[12];
lean_object* v_a_1874_ = _args[13];
lean_object* v_a_1875_ = _args[14];
lean_object* v_a_1876_ = _args[15];
lean_object* v_a_1877_ = _args[16];
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1861_, v_parentInst_x3f_1862_, v_childInst_x3f_1863_, v_toFieldName_1864_, v_u_1865_, v_type_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec(v_a_1867_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1879_, lean_object* v_inst_1880_, lean_object* v_toFieldName_1881_, lean_object* v_u_1882_, lean_object* v_type_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_toField_1892_; lean_object* v___x_1893_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1890_, 0, v_u_1882_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_mkConst(v_toFieldName_1881_, v___x_1890_);
v_toField_1892_ = l_Lean_mkAppB(v___x_1891_, v_type_1883_, v_inst_1880_);
v___x_1893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1879_, v_toField_1892_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1894_, lean_object* v_inst_1895_, lean_object* v_toFieldName_1896_, lean_object* v_u_1897_, lean_object* v_type_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1894_, v_inst_1895_, v_toFieldName_1896_, v_u_1897_, v_type_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1905_, lean_object* v_inst_1906_, lean_object* v_toFieldName_1907_, lean_object* v_u_1908_, lean_object* v_type_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1905_, v_inst_1906_, v_toFieldName_1907_, v_u_1908_, v_type_1909_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1922_, lean_object* v_inst_1923_, lean_object* v_toFieldName_1924_, lean_object* v_u_1925_, lean_object* v_type_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1922_, v_inst_1923_, v_toFieldName_1924_, v_u_1925_, v_type_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
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
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1939_, lean_object* v_inst_1940_, lean_object* v_toFieldName_1941_, lean_object* v_toHeteroName_1942_, lean_object* v_u_1943_, lean_object* v_type_1944_, lean_object* v_extraType_x3f_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_toField_1954_; 
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_u_1943_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
lean_inc_ref(v___x_1952_);
v___x_1953_ = l_Lean_mkConst(v_toFieldName_1941_, v___x_1952_);
lean_inc_ref(v_type_1944_);
v_toField_1954_ = l_Lean_mkAppB(v___x_1953_, v_type_1944_, v_inst_1940_);
if (lean_obj_tag(v_extraType_x3f_1945_) == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = l_Lean_mkConst(v_toHeteroName_1942_, v___x_1952_);
v___x_1956_ = l_Lean_mkAppB(v___x_1955_, v_type_1944_, v_toField_1954_);
v___x_1957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1939_, v___x_1956_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1957_;
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_val_1958_ = lean_ctor_get(v_extraType_x3f_1945_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v_extraType_x3f_1945_, 1);
v___x_1959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1952_);
v___x_1961_ = l_Lean_mkConst(v_toHeteroName_1942_, v___x_1960_);
v___x_1962_ = l_Lean_mkApp3(v___x_1961_, v_val_1958_, v_type_1944_, v_toField_1954_);
v___x_1963_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1939_, v___x_1962_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1964_, lean_object* v_inst_1965_, lean_object* v_toFieldName_1966_, lean_object* v_toHeteroName_1967_, lean_object* v_u_1968_, lean_object* v_type_1969_, lean_object* v_extraType_x3f_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1964_, v_inst_1965_, v_toFieldName_1966_, v_toHeteroName_1967_, v_u_1968_, v_type_1969_, v_extraType_x3f_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1977_, lean_object* v_inst_1978_, lean_object* v_toFieldName_1979_, lean_object* v_toHeteroName_1980_, lean_object* v_u_1981_, lean_object* v_type_1982_, lean_object* v_extraType_x3f_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1977_, v_inst_1978_, v_toFieldName_1979_, v_toHeteroName_1980_, v_u_1981_, v_type_1982_, v_extraType_x3f_1983_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_1996_ = _args[0];
lean_object* v_inst_1997_ = _args[1];
lean_object* v_toFieldName_1998_ = _args[2];
lean_object* v_toHeteroName_1999_ = _args[3];
lean_object* v_u_2000_ = _args[4];
lean_object* v_type_2001_ = _args[5];
lean_object* v_extraType_x3f_2002_ = _args[6];
lean_object* v_a_2003_ = _args[7];
lean_object* v_a_2004_ = _args[8];
lean_object* v_a_2005_ = _args[9];
lean_object* v_a_2006_ = _args[10];
lean_object* v_a_2007_ = _args[11];
lean_object* v_a_2008_ = _args[12];
lean_object* v_a_2009_ = _args[13];
lean_object* v_a_2010_ = _args[14];
lean_object* v_a_2011_ = _args[15];
lean_object* v_a_2012_ = _args[16];
lean_object* v_a_2013_ = _args[17];
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_1996_, v_inst_1997_, v_toFieldName_1998_, v_toHeteroName_1999_, v_u_2000_, v_type_2001_, v_extraType_x3f_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec(v_a_2003_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2019_, lean_object* v_type_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v_smulType_2036_; lean_object* v___x_2037_; 
v___x_2028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2030_ = lean_box(0);
lean_inc(v_u_2019_);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_u_2019_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_u_2019_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2029_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_inc_ref(v___x_2033_);
v___x_2034_ = l_Lean_mkConst(v___x_2028_, v___x_2033_);
v___x_2035_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2020_, 2);
v_smulType_2036_ = l_Lean_mkApp3(v___x_2034_, v___x_2035_, v_type_2020_, v_type_2020_);
v___x_2037_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2036_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2074_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2074_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2074_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2069_; 
lean_del_object(v___x_2040_);
v_val_2042_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2069_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2069_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2047_ = l_Lean_mkConst(v___x_2046_, v___x_2033_);
lean_inc_ref(v_type_2020_);
v___x_2048_ = l_Lean_mkApp4(v___x_2047_, v___x_2035_, v_type_2020_, v_type_2020_, v_val_2042_);
v___x_2049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2048_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2060_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_a_2050_);
v___x_2055_ = v___x_2044_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2044_);
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2049_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2049_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
lean_dec(v_a_2038_);
lean_dec_ref_known(v___x_2033_, 2);
lean_dec_ref(v_type_2020_);
v___x_2070_ = lean_box(0);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2070_);
v___x_2072_ = v___x_2040_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2033_, 2);
lean_dec_ref(v_type_2020_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2075_, lean_object* v_type_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2075_, v_type_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2085_, lean_object* v_type_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2085_, v_type_2086_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2099_, lean_object* v_type_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2099_, v_type_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec(v_a_2101_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2113_, lean_object* v_type_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_smulType_2130_; lean_object* v___x_2131_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2124_ = lean_box(0);
lean_inc(v_u_2113_);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_u_2113_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_u_2113_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2123_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
lean_inc_ref(v___x_2127_);
v___x_2128_ = l_Lean_mkConst(v___x_2122_, v___x_2127_);
v___x_2129_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2114_, 2);
v_smulType_2130_ = l_Lean_mkApp3(v___x_2128_, v___x_2129_, v_type_2114_, v_type_2114_);
v___x_2131_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2130_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2168_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2168_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2168_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
if (lean_obj_tag(v_a_2132_) == 1)
{
lean_object* v_val_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2134_);
v_val_2136_ = lean_ctor_get(v_a_2132_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_a_2132_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2138_ = v_a_2132_;
v_isShared_2139_ = v_isSharedCheck_2163_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_val_2136_);
lean_dec(v_a_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2163_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2127_);
lean_inc_ref(v_type_2114_);
v___x_2142_ = l_Lean_mkApp4(v___x_2141_, v___x_2129_, v_type_2114_, v_type_2114_, v_val_2136_);
v___x_2143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2142_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2154_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2154_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v_a_2144_);
v___x_2149_ = v___x_2138_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
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
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2138_);
v_a_2155_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2143_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2143_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec(v_a_2132_);
lean_dec_ref_known(v___x_2127_, 2);
lean_dec_ref(v_type_2114_);
v___x_2164_ = lean_box(0);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2164_);
v___x_2166_ = v___x_2134_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2127_, 2);
lean_dec_ref(v_type_2114_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2169_, lean_object* v_type_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2169_, v_type_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2179_, lean_object* v_type_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2179_, v_type_2180_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2193_, lean_object* v_type_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2193_, v_type_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec(v_a_2195_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_ks_2211_; lean_object* v_vs_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2236_; 
v_ks_2211_ = lean_ctor_get(v_x_2207_, 0);
v_vs_2212_ = lean_ctor_get(v_x_2207_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_x_2207_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2214_ = v_x_2207_;
v_isShared_2215_ = v_isSharedCheck_2236_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_vs_2212_);
lean_inc(v_ks_2211_);
lean_dec(v_x_2207_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2236_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_get_size(v_ks_2211_);
v___x_2217_ = lean_nat_dec_lt(v_x_2208_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
lean_dec(v_x_2208_);
v___x_2218_ = lean_array_push(v_ks_2211_, v_x_2209_);
v___x_2219_ = lean_array_push(v_vs_2212_, v_x_2210_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2219_);
lean_ctor_set(v___x_2214_, 0, v___x_2218_);
v___x_2221_ = v___x_2214_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
else
{
lean_object* v_k_x27_2223_; uint8_t v___x_2224_; 
v_k_x27_2223_ = lean_array_fget_borrowed(v_ks_2211_, v_x_2208_);
v___x_2224_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2209_, v_k_x27_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2226_; 
if (v_isShared_2215_ == 0)
{
v___x_2226_ = v___x_2214_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_ks_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_vs_2212_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_add(v_x_2208_, v___x_2227_);
lean_dec(v_x_2208_);
v_x_2207_ = v___x_2226_;
v_x_2208_ = v___x_2228_;
goto _start;
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = lean_array_fset(v_ks_2211_, v_x_2208_, v_x_2209_);
v___x_2232_ = lean_array_fset(v_vs_2212_, v_x_2208_, v_x_2210_);
lean_dec(v_x_2208_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2232_);
lean_ctor_set(v___x_2214_, 0, v___x_2231_);
v___x_2234_ = v___x_2214_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2237_, lean_object* v_k_2238_, lean_object* v_v_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2237_, v___x_2240_, v_k_2238_, v_v_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2243_, size_t v_x_2244_, size_t v_x_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_){
_start:
{
if (lean_obj_tag(v_x_2243_) == 0)
{
lean_object* v_es_2248_; size_t v___x_2249_; size_t v___x_2250_; lean_object* v_j_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_es_2248_ = lean_ctor_get(v_x_2243_, 0);
v___x_2249_ = ((size_t)31ULL);
v___x_2250_ = lean_usize_land(v_x_2244_, v___x_2249_);
v_j_2251_ = lean_usize_to_nat(v___x_2250_);
v___x_2252_ = lean_array_get_size(v_es_2248_);
v___x_2253_ = lean_nat_dec_lt(v_j_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_dec(v_j_2251_);
lean_dec(v_x_2247_);
lean_dec_ref(v_x_2246_);
return v_x_2243_;
}
else
{
lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2292_; 
lean_inc_ref(v_es_2248_);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_x_2243_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; 
v_unused_2293_ = lean_ctor_get(v_x_2243_, 0);
lean_dec(v_unused_2293_);
v___x_2255_ = v_x_2243_;
v_isShared_2256_ = v_isSharedCheck_2292_;
goto v_resetjp_2254_;
}
else
{
lean_dec(v_x_2243_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2292_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_v_2257_; lean_object* v___x_2258_; lean_object* v_xs_x27_2259_; lean_object* v___y_2261_; 
v_v_2257_ = lean_array_fget(v_es_2248_, v_j_2251_);
v___x_2258_ = lean_box(0);
v_xs_x27_2259_ = lean_array_fset(v_es_2248_, v_j_2251_, v___x_2258_);
switch(lean_obj_tag(v_v_2257_))
{
case 0:
{
lean_object* v_key_2266_; lean_object* v_val_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2277_; 
v_key_2266_ = lean_ctor_get(v_v_2257_, 0);
v_val_2267_ = lean_ctor_get(v_v_2257_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_v_2257_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2269_ = v_v_2257_;
v_isShared_2270_ = v_isSharedCheck_2277_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_val_2267_);
lean_inc(v_key_2266_);
lean_dec(v_v_2257_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2277_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
uint8_t v___x_2271_; 
v___x_2271_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2246_, v_key_2266_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_del_object(v___x_2269_);
v___x_2272_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2266_, v_val_2267_, v_x_2246_, v_x_2247_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
v___y_2261_ = v___x_2273_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2275_; 
lean_dec(v_val_2267_);
lean_dec(v_key_2266_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v_x_2247_);
lean_ctor_set(v___x_2269_, 0, v_x_2246_);
v___x_2275_ = v___x_2269_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_x_2246_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_x_2247_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
v___y_2261_ = v___x_2275_;
goto v___jp_2260_;
}
}
}
}
case 1:
{
lean_object* v_node_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2290_; 
v_node_2278_ = lean_ctor_get(v_v_2257_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_v_2257_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2280_ = v_v_2257_;
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_node_2278_);
lean_dec(v_v_2257_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2282_ = ((size_t)5ULL);
v___x_2283_ = lean_usize_shift_right(v_x_2244_, v___x_2282_);
v___x_2284_ = ((size_t)1ULL);
v___x_2285_ = lean_usize_add(v_x_2245_, v___x_2284_);
v___x_2286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2278_, v___x_2283_, v___x_2285_, v_x_2246_, v_x_2247_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2286_);
v___x_2288_ = v___x_2280_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
v___y_2261_ = v___x_2288_;
goto v___jp_2260_;
}
}
}
default: 
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_x_2246_);
lean_ctor_set(v___x_2291_, 1, v_x_2247_);
v___y_2261_ = v___x_2291_;
goto v___jp_2260_;
}
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_array_fset(v_xs_x27_2259_, v_j_2251_, v___y_2261_);
lean_dec(v_j_2251_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2262_);
v___x_2264_ = v___x_2255_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
else
{
lean_object* v_ks_2294_; lean_object* v_vs_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2315_; 
v_ks_2294_ = lean_ctor_get(v_x_2243_, 0);
v_vs_2295_ = lean_ctor_get(v_x_2243_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2243_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2297_ = v_x_2243_;
v_isShared_2298_ = v_isSharedCheck_2315_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_vs_2295_);
lean_inc(v_ks_2294_);
lean_dec(v_x_2243_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2315_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_ks_2294_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_vs_2295_);
v___x_2300_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v_newNode_2301_; uint8_t v___y_2303_; size_t v___x_2309_; uint8_t v___x_2310_; 
v_newNode_2301_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2300_, v_x_2246_, v_x_2247_);
v___x_2309_ = ((size_t)7ULL);
v___x_2310_ = lean_usize_dec_le(v___x_2309_, v_x_2245_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2301_);
v___x_2312_ = lean_unsigned_to_nat(4u);
v___x_2313_ = lean_nat_dec_lt(v___x_2311_, v___x_2312_);
lean_dec(v___x_2311_);
v___y_2303_ = v___x_2313_;
goto v___jp_2302_;
}
else
{
v___y_2303_ = v___x_2310_;
goto v___jp_2302_;
}
v___jp_2302_:
{
if (v___y_2303_ == 0)
{
lean_object* v_ks_2304_; lean_object* v_vs_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_ks_2304_ = lean_ctor_get(v_newNode_2301_, 0);
lean_inc_ref(v_ks_2304_);
v_vs_2305_ = lean_ctor_get(v_newNode_2301_, 1);
lean_inc_ref(v_vs_2305_);
lean_dec_ref(v_newNode_2301_);
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2245_, v_ks_2304_, v_vs_2305_, v___x_2306_, v___x_2307_);
lean_dec_ref(v_vs_2305_);
lean_dec_ref(v_ks_2304_);
return v___x_2308_;
}
else
{
return v_newNode_2301_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2316_, lean_object* v_keys_2317_, lean_object* v_vals_2318_, lean_object* v_i_2319_, lean_object* v_entries_2320_){
_start:
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_array_get_size(v_keys_2317_);
v___x_2322_ = lean_nat_dec_lt(v_i_2319_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_dec(v_i_2319_);
return v_entries_2320_;
}
else
{
lean_object* v_k_2323_; lean_object* v_v_2324_; uint64_t v___x_2325_; size_t v_h_2326_; size_t v___x_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; size_t v_h_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_k_2323_ = lean_array_fget_borrowed(v_keys_2317_, v_i_2319_);
v_v_2324_ = lean_array_fget_borrowed(v_vals_2318_, v_i_2319_);
v___x_2325_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2323_);
v_h_2326_ = lean_uint64_to_usize(v___x_2325_);
v___x_2327_ = ((size_t)5ULL);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_sub(v_depth_2316_, v___x_2329_);
v___x_2331_ = lean_usize_mul(v___x_2327_, v___x_2330_);
v_h_2332_ = lean_usize_shift_right(v_h_2326_, v___x_2331_);
v___x_2333_ = lean_nat_add(v_i_2319_, v___x_2328_);
lean_dec(v_i_2319_);
lean_inc(v_v_2324_);
lean_inc(v_k_2323_);
v___x_2334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2320_, v_h_2332_, v_depth_2316_, v_k_2323_, v_v_2324_);
v_i_2319_ = v___x_2333_;
v_entries_2320_ = v___x_2334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2336_, lean_object* v_keys_2337_, lean_object* v_vals_2338_, lean_object* v_i_2339_, lean_object* v_entries_2340_){
_start:
{
size_t v_depth_boxed_2341_; lean_object* v_res_2342_; 
v_depth_boxed_2341_ = lean_unbox_usize(v_depth_2336_);
lean_dec(v_depth_2336_);
v_res_2342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2341_, v_keys_2337_, v_vals_2338_, v_i_2339_, v_entries_2340_);
lean_dec_ref(v_vals_2338_);
lean_dec_ref(v_keys_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
size_t v_x_575381__boxed_2348_; size_t v_x_575382__boxed_2349_; lean_object* v_res_2350_; 
v_x_575381__boxed_2348_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_x_575382__boxed_2349_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_res_2350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2343_, v_x_575381__boxed_2348_, v_x_575382__boxed_2349_, v_x_2346_, v_x_2347_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_){
_start:
{
uint64_t v___x_2354_; size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2352_);
v___x_2355_ = lean_uint64_to_usize(v___x_2354_);
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2351_, v___x_2355_, v___x_2356_, v_x_2352_, v_x_2353_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2358_, lean_object* v_s_2359_){
_start:
{
lean_object* v_structs_2360_; lean_object* v_typeIdOf_2361_; lean_object* v_exprToStructId_2362_; lean_object* v_exprToStructIdEntries_2363_; lean_object* v_forbiddenNatModules_2364_; lean_object* v_natStructs_2365_; lean_object* v_natTypeIdOf_2366_; lean_object* v_exprToNatStructId_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2376_; 
v_structs_2360_ = lean_ctor_get(v_s_2359_, 0);
v_typeIdOf_2361_ = lean_ctor_get(v_s_2359_, 1);
v_exprToStructId_2362_ = lean_ctor_get(v_s_2359_, 2);
v_exprToStructIdEntries_2363_ = lean_ctor_get(v_s_2359_, 3);
v_forbiddenNatModules_2364_ = lean_ctor_get(v_s_2359_, 4);
v_natStructs_2365_ = lean_ctor_get(v_s_2359_, 5);
v_natTypeIdOf_2366_ = lean_ctor_get(v_s_2359_, 6);
v_exprToNatStructId_2367_ = lean_ctor_get(v_s_2359_, 7);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_s_2359_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2369_ = v_s_2359_;
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_exprToNatStructId_2367_);
lean_inc(v_natTypeIdOf_2366_);
lean_inc(v_natStructs_2365_);
lean_inc(v_forbiddenNatModules_2364_);
lean_inc(v_exprToStructIdEntries_2363_);
lean_inc(v_exprToStructId_2362_);
lean_inc(v_typeIdOf_2361_);
lean_inc(v_structs_2360_);
lean_dec(v_s_2359_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2364_, v_type_2358_, v___x_2371_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 4, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_structs_2360_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_typeIdOf_2361_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_exprToStructId_2362_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_exprToStructIdEntries_2363_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2375_, 5, v_natStructs_2365_);
lean_ctor_set(v_reuseFailAlloc_2375_, 6, v_natTypeIdOf_2366_);
lean_ctor_set(v_reuseFailAlloc_2375_, 7, v_exprToNatStructId_2367_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v_a_2377_, lean_object* v_00___2378_){
_start:
{
if (lean_obj_tag(v_a_2377_) == 0)
{
uint8_t v___x_2379_; 
v___x_2379_ = 0;
return v___x_2379_;
}
else
{
uint8_t v___x_2380_; 
v___x_2380_ = 1;
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object* v_a_2381_, lean_object* v_00___2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2381_, v_00___2382_);
lean_dec(v_a_2381_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v___x_2385_, lean_object* v_s_2386_){
_start:
{
lean_object* v_structs_2387_; lean_object* v_typeIdOf_2388_; lean_object* v_exprToStructId_2389_; lean_object* v_exprToStructIdEntries_2390_; lean_object* v_forbiddenNatModules_2391_; lean_object* v_natStructs_2392_; lean_object* v_natTypeIdOf_2393_; lean_object* v_exprToNatStructId_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_structs_2387_ = lean_ctor_get(v_s_2386_, 0);
v_typeIdOf_2388_ = lean_ctor_get(v_s_2386_, 1);
v_exprToStructId_2389_ = lean_ctor_get(v_s_2386_, 2);
v_exprToStructIdEntries_2390_ = lean_ctor_get(v_s_2386_, 3);
v_forbiddenNatModules_2391_ = lean_ctor_get(v_s_2386_, 4);
v_natStructs_2392_ = lean_ctor_get(v_s_2386_, 5);
v_natTypeIdOf_2393_ = lean_ctor_get(v_s_2386_, 6);
v_exprToNatStructId_2394_ = lean_ctor_get(v_s_2386_, 7);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_s_2386_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v_s_2386_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_exprToNatStructId_2394_);
lean_inc(v_natTypeIdOf_2393_);
lean_inc(v_natStructs_2392_);
lean_inc(v_forbiddenNatModules_2391_);
lean_inc(v_exprToStructIdEntries_2390_);
lean_inc(v_exprToStructId_2389_);
lean_inc(v_typeIdOf_2388_);
lean_inc(v_structs_2387_);
lean_dec(v_s_2386_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_array_push(v_structs_2387_, v___x_2385_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_typeIdOf_2388_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_exprToStructId_2389_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_exprToStructIdEntries_2390_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_forbiddenNatModules_2391_);
lean_ctor_set(v_reuseFailAlloc_2401_, 5, v_natStructs_2392_);
lean_ctor_set(v_reuseFailAlloc_2401_, 6, v_natTypeIdOf_2393_);
lean_ctor_set(v_reuseFailAlloc_2401_, 7, v_exprToNatStructId_2394_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_unsigned_to_nat(32u);
v___x_2410_ = lean_mk_empty_array_with_capacity(v___x_2409_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Lean_mkRawNatLit(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = l_Lean_Int_mkType;
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = l_Lean_Nat_mkType;
v___x_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___y_2536_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___x_2601_; 
lean_inc_ref(v_type_2523_);
v___x_2601_ = l_Lean_Meta_getDecLevel_x3f(v_type_2523_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_3519_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_3519_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_3519_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
if (lean_obj_tag(v_a_2602_) == 1)
{
lean_object* v_val_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_3514_; 
lean_del_object(v___x_2604_);
v_val_2606_ = lean_ctor_get(v_a_2602_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_2608_ = v_a_2602_;
v_isShared_2609_ = v_isSharedCheck_3514_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_val_2606_);
lean_dec(v_a_2602_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_3514_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; 
lean_inc_ref(v_type_2523_);
v___x_2610_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_3513_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_3513_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_3513_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2616_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2615_, v_val_2606_, v_type_2523_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2619_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2618_, v_val_2606_, v_type_2523_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc_n(v_a_2620_, 2);
lean_dec_ref_known(v___x_2619_, 1);
lean_inc(v_a_2617_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2621_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_2620_, v_a_2617_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v_homomulFn_x3f_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; uint8_t v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v_ltFn_x3f_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v_leFn_x3f_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v_charInst_x3f_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___x_3134_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
lean_inc(v_a_2617_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3134_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_2617_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
lean_inc(v_a_2617_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3136_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_2617_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
lean_inc(v_a_2617_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3138_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_2617_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; uint8_t v___y_3161_; lean_object* v___x_3248_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3248_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2526_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; uint8_t v_ring_3250_; lean_object* v___f_3251_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; uint8_t v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3329_; uint8_t v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; uint8_t v___y_3350_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v_ring_3250_ = lean_ctor_get_uint8(v_a_3249_, sizeof(void*)*13 + 21);
lean_dec(v_a_3249_);
lean_inc_ref(v_type_2523_);
v___f_3251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3251_, 0, v_type_2523_);
if (v_ring_3250_ == 0)
{
v___y_3350_ = v_ring_3250_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2611_, v___x_3435_);
if (v___x_3436_ == 0)
{
v___y_3350_ = v___x_3436_;
goto v___jp_3349_;
}
else
{
if (lean_obj_tag(v_a_3135_) == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v___x_3437_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3438_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3437_, v___f_3251_, v_a_2524_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3446_; 
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3447_);
v___x_3440_ = v___x_3438_;
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v___x_3438_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_box(0);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3442_);
v___x_3444_ = v___x_3440_;
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
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
v_a_3448_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3438_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3438_);
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
uint8_t v___x_3456_; 
v___x_3456_ = 0;
v___y_3350_ = v___x_3456_;
goto v___jp_3349_;
}
}
}
v___jp_3252_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3255_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; uint8_t v_ring_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_ring_3276_ = lean_ctor_get_uint8(v_a_3275_, sizeof(void*)*13 + 21);
lean_dec(v_a_3275_);
if (v_ring_3276_ == 0)
{
lean_dec_ref(v___f_3251_);
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3260_;
v___y_3149_ = v___y_3262_;
v___y_3150_ = v___y_3273_;
v___y_3151_ = v___y_3263_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3266_;
v___y_3154_ = v___y_3264_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3268_;
v___y_3157_ = v___y_3271_;
v___y_3158_ = v___y_3270_;
v___y_3159_ = v___y_3269_;
v___y_3160_ = v___y_3272_;
v___y_3161_ = v_ring_3276_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = lean_box(0);
v___x_3278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2611_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_dec_ref(v___f_3251_);
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3260_;
v___y_3149_ = v___y_3262_;
v___y_3150_ = v___y_3273_;
v___y_3151_ = v___y_3263_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3266_;
v___y_3154_ = v___y_3264_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3268_;
v___y_3157_ = v___y_3271_;
v___y_3158_ = v___y_3270_;
v___y_3159_ = v___y_3269_;
v___y_3160_ = v___y_3272_;
v___y_3161_ = v___x_3278_;
goto v___jp_3140_;
}
else
{
if (lean_obj_tag(v___y_3273_) == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3259_);
lean_dec(v___y_3256_);
lean_dec(v___y_3253_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v___x_3279_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3280_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3279_, v___f_3251_, v___y_3264_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3288_; 
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3289_);
v___x_3282_ = v___x_3280_;
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v___x_3280_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3288_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = lean_box(0);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3280_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3280_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_dec_ref(v___f_3251_);
v___y_3141_ = v___y_3253_;
v___y_3142_ = v___y_3254_;
v___y_3143_ = v___y_3255_;
v___y_3144_ = v___y_3256_;
v___y_3145_ = v___y_3257_;
v___y_3146_ = v___y_3258_;
v___y_3147_ = v___y_3259_;
v___y_3148_ = v___y_3260_;
v___y_3149_ = v___y_3262_;
v___y_3150_ = v___y_3273_;
v___y_3151_ = v___y_3263_;
v___y_3152_ = v___y_3265_;
v___y_3153_ = v___y_3266_;
v___y_3154_ = v___y_3264_;
v___y_3155_ = v___y_3267_;
v___y_3156_ = v___y_3268_;
v___y_3157_ = v___y_3271_;
v___y_3158_ = v___y_3270_;
v___y_3159_ = v___y_3269_;
v___y_3160_ = v___y_3272_;
v___y_3161_ = v___y_3261_;
goto v___jp_3140_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3259_);
lean_dec(v___y_3256_);
lean_dec(v___y_3253_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3298_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3274_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3274_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
v___jp_3306_:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_box(0);
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
v___y_3263_ = v___y_3317_;
v___y_3264_ = v___y_3320_;
v___y_3265_ = v___y_3319_;
v___y_3266_ = v___y_3318_;
v___y_3267_ = v___y_3321_;
v___y_3268_ = v___y_3322_;
v___y_3269_ = v___y_3325_;
v___y_3270_ = v___y_3324_;
v___y_3271_ = v___y_3323_;
v___y_3272_ = v___y_3326_;
v___y_3273_ = v___x_3327_;
goto v___jp_3252_;
}
v___jp_3328_:
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_box(0);
v___y_3307_ = v___y_3329_;
v___y_3308_ = v___y_3343_;
v___y_3309_ = v___y_3340_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___y_3339_;
v___y_3312_ = v___y_3341_;
v___y_3313_ = v___y_3337_;
v___y_3314_ = v___y_3344_;
v___y_3315_ = v___y_3330_;
v___y_3316_ = v___y_3331_;
v___y_3317_ = v___y_3347_;
v___y_3318_ = v___y_3332_;
v___y_3319_ = v___y_3346_;
v___y_3320_ = v___y_3338_;
v___y_3321_ = v___y_3333_;
v___y_3322_ = v___y_3334_;
v___y_3323_ = v___y_3335_;
v___y_3324_ = v___y_3342_;
v___y_3325_ = v___y_3345_;
v___y_3326_ = v___x_3348_;
goto v___jp_3306_;
}
v___jp_3349_:
{
lean_object* v___x_3351_; 
lean_inc(v_a_2611_);
v___x_3351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2611_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc_n(v_a_3352_, 2);
lean_dec_ref_known(v___x_3351_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_3352_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_n(v_a_3354_, 2);
lean_dec_ref_known(v___x_3353_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_3354_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3410_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3410_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3410_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
if (lean_obj_tag(v_a_3356_) == 1)
{
lean_object* v_val_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_del_object(v___x_3358_);
v_val_3360_ = lean_ctor_get(v_a_3356_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_a_3356_, 1);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3361_, v_val_2606_, v_type_2523_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc_n(v_a_3363_, 2);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3365_ = lean_box(0);
lean_inc_n(v_val_2606_, 3);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_val_2606_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
lean_inc_ref(v___x_3366_);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_val_2606_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_inc_ref(v___x_3367_);
v___x_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_val_2606_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
lean_inc_ref(v___x_3368_);
v___x_3369_ = l_Lean_mkConst(v___x_3364_, v___x_3368_);
lean_inc_ref_n(v_type_2523_, 3);
v___x_3370_ = l_Lean_mkApp4(v___x_3369_, v_type_2523_, v_type_2523_, v_type_2523_, v_a_3363_);
v___x_3371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3370_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3371_) == 0)
{
if (lean_obj_tag(v_a_2617_) == 1)
{
if (lean_obj_tag(v_a_3135_) == 1)
{
lean_object* v_a_3372_; lean_object* v_val_3373_; lean_object* v_val_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v_val_3373_ = lean_ctor_get(v_a_2617_, 0);
v_val_3374_ = lean_ctor_get(v_a_3135_, 0);
v___x_3375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3366_);
v___x_3376_ = l_Lean_mkConst(v___x_3375_, v___x_3366_);
lean_inc(v_val_3374_);
lean_inc(v_val_3373_);
lean_inc(v_a_3363_);
lean_inc_ref(v_type_2523_);
v___x_3377_ = l_Lean_mkApp4(v___x_3376_, v_type_2523_, v_a_3363_, v_val_3373_, v_val_3374_);
v___x_3378_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3377_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
if (lean_obj_tag(v_a_3379_) == 0)
{
lean_dec_ref_known(v_a_3135_, 1);
v___y_3307_ = v___x_3368_;
v___y_3308_ = v_a_2529_;
v___y_3309_ = v_a_2526_;
v___y_3310_ = v_a_3354_;
v___y_3311_ = v_a_2525_;
v___y_3312_ = v_a_2527_;
v___y_3313_ = v___x_3366_;
v___y_3314_ = v_a_2530_;
v___y_3315_ = v___y_3350_;
v___y_3316_ = v_a_3372_;
v___y_3317_ = v_a_2533_;
v___y_3318_ = v_val_3360_;
v___y_3319_ = v_a_2532_;
v___y_3320_ = v_a_2524_;
v___y_3321_ = v_a_3363_;
v___y_3322_ = v_a_3352_;
v___y_3323_ = v___x_3367_;
v___y_3324_ = v_a_2528_;
v___y_3325_ = v_a_2531_;
v___y_3326_ = v_a_3379_;
goto v___jp_3306_;
}
else
{
if (v___y_3350_ == 0)
{
v___y_3253_ = v___x_3368_;
v___y_3254_ = v_a_2529_;
v___y_3255_ = v_a_2526_;
v___y_3256_ = v_a_3354_;
v___y_3257_ = v_a_2525_;
v___y_3258_ = v_a_2527_;
v___y_3259_ = v___x_3366_;
v___y_3260_ = v_a_2530_;
v___y_3261_ = v___y_3350_;
v___y_3262_ = v_a_3372_;
v___y_3263_ = v_a_2533_;
v___y_3264_ = v_a_2524_;
v___y_3265_ = v_a_2532_;
v___y_3266_ = v_val_3360_;
v___y_3267_ = v_a_3363_;
v___y_3268_ = v_a_3352_;
v___y_3269_ = v_a_2531_;
v___y_3270_ = v_a_2528_;
v___y_3271_ = v___x_3367_;
v___y_3272_ = v_a_3379_;
v___y_3273_ = v_a_3135_;
goto v___jp_3252_;
}
else
{
lean_dec_ref_known(v_a_3135_, 1);
v___y_3307_ = v___x_3368_;
v___y_3308_ = v_a_2529_;
v___y_3309_ = v_a_2526_;
v___y_3310_ = v_a_3354_;
v___y_3311_ = v_a_2525_;
v___y_3312_ = v_a_2527_;
v___y_3313_ = v___x_3366_;
v___y_3314_ = v_a_2530_;
v___y_3315_ = v___y_3350_;
v___y_3316_ = v_a_3372_;
v___y_3317_ = v_a_2533_;
v___y_3318_ = v_val_3360_;
v___y_3319_ = v_a_2532_;
v___y_3320_ = v_a_2524_;
v___y_3321_ = v_a_3363_;
v___y_3322_ = v_a_3352_;
v___y_3323_ = v___x_3367_;
v___y_3324_ = v_a_2528_;
v___y_3325_ = v_a_2531_;
v___y_3326_ = v_a_3379_;
goto v___jp_3306_;
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref_known(v_a_3135_, 1);
lean_dec(v_a_3372_);
lean_dec_ref_known(v_a_2617_, 1);
lean_dec_ref_known(v___x_3368_, 2);
lean_dec_ref_known(v___x_3367_, 2);
lean_dec_ref_known(v___x_3366_, 2);
lean_dec(v_a_3363_);
lean_dec(v_val_3360_);
lean_dec(v_a_3354_);
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3380_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3378_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3378_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_a_3388_; 
lean_dec(v_a_3135_);
v_a_3388_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3371_, 1);
v___y_3329_ = v___x_3368_;
v___y_3330_ = v___y_3350_;
v___y_3331_ = v_a_3388_;
v___y_3332_ = v_val_3360_;
v___y_3333_ = v_a_3363_;
v___y_3334_ = v_a_3352_;
v___y_3335_ = v___x_3367_;
v___y_3336_ = v_a_3354_;
v___y_3337_ = v___x_3366_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
v___y_3344_ = v_a_2530_;
v___y_3345_ = v_a_2531_;
v___y_3346_ = v_a_2532_;
v___y_3347_ = v_a_2533_;
goto v___jp_3328_;
}
}
else
{
lean_object* v_a_3389_; 
lean_dec(v_a_3135_);
v_a_3389_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3371_, 1);
v___y_3329_ = v___x_3368_;
v___y_3330_ = v___y_3350_;
v___y_3331_ = v_a_3389_;
v___y_3332_ = v_val_3360_;
v___y_3333_ = v_a_3363_;
v___y_3334_ = v_a_3352_;
v___y_3335_ = v___x_3367_;
v___y_3336_ = v_a_3354_;
v___y_3337_ = v___x_3366_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
v___y_3344_ = v_a_2530_;
v___y_3345_ = v_a_2531_;
v___y_3346_ = v_a_2532_;
v___y_3347_ = v_a_2533_;
goto v___jp_3328_;
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref_known(v___x_3368_, 2);
lean_dec_ref_known(v___x_3367_, 2);
lean_dec_ref_known(v___x_3366_, 2);
lean_dec(v_a_3363_);
lean_dec(v_val_3360_);
lean_dec(v_a_3354_);
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3390_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3371_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3371_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_val_3360_);
lean_dec(v_a_3354_);
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3398_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3362_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3362_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_dec(v_a_3356_);
lean_dec(v_a_3354_);
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v___x_3406_ = lean_box(0);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3406_);
v___x_3408_ = v___x_3358_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_a_3354_);
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3411_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3355_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3355_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_a_3352_);
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3419_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3353_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3353_);
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
lean_dec_ref(v___f_3251_);
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3427_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3351_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3351_);
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
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_a_3139_);
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3457_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3248_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3248_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
v___jp_3140_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc(v___y_3150_);
lean_inc(v_a_2617_);
v___x_3163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2617_, v___y_3150_, v_a_3137_, v___x_3162_, v_val_2606_, v_type_2523_, v___y_3158_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc(v_a_2617_);
v___x_3166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2617_, v_a_3164_, v_a_3139_, v___x_3165_, v_val_2606_, v_type_2523_, v___y_3158_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3166_, 1);
v___x_3168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3147_, 2);
v___x_3172_ = l_Lean_mkConst(v___x_3171_, v___y_3147_);
lean_inc_ref(v___y_3153_);
lean_inc_ref_n(v_type_2523_, 3);
v___x_3173_ = l_Lean_mkAppB(v___x_3172_, v_type_2523_, v___y_3153_);
v___x_3174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3176_ = l_Lean_mkConst(v___x_3175_, v___y_3147_);
lean_inc_ref(v___x_3173_);
v___x_3177_ = l_Lean_mkAppB(v___x_3176_, v_type_2523_, v___x_3173_);
lean_inc(v___y_3144_);
lean_inc(v_val_2606_);
v___x_3178_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2606_, v_type_2523_, v___y_3144_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3180_, v_val_2606_, v_type_2523_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2606_, v_type_2523_, v___y_3154_, v___y_3145_, v___y_3143_, v___y_3146_, v___y_3158_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
lean_inc(v___y_3150_);
lean_inc(v_a_2620_);
lean_inc(v_a_2617_);
lean_inc(v_a_3179_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2606_, v_type_2523_, v_a_3179_, v_a_2617_, v_a_2620_, v___y_3150_, v___y_3158_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3185_) == 0)
{
if (lean_obj_tag(v_a_3179_) == 1)
{
lean_object* v_a_3186_; lean_object* v_val_3187_; lean_object* v___x_3188_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v_val_3187_ = lean_ctor_get(v_a_3179_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v_a_3179_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_3188_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2606_, v_type_2523_, v_val_3187_, v___y_3154_, v___y_3145_, v___y_3143_, v___y_3146_, v___y_3158_, v___y_3142_, v___y_3148_, v___y_3159_, v___y_3152_, v___y_3151_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___y_2832_ = v___y_3141_;
v___y_2833_ = v___x_3169_;
v___y_2834_ = v___x_3168_;
v___y_2835_ = v___y_3144_;
v___y_2836_ = v_a_3182_;
v___y_2837_ = v___y_3147_;
v___y_2838_ = v___y_3161_;
v___y_2839_ = v___y_3149_;
v___y_2840_ = v___y_3150_;
v___y_2841_ = v___x_3173_;
v___y_2842_ = v_a_3167_;
v___y_2843_ = v___y_3153_;
v___y_2844_ = v_a_3186_;
v___y_2845_ = v___y_3155_;
v___y_2846_ = v_a_3184_;
v___y_2847_ = v___y_3156_;
v___y_2848_ = v___y_3157_;
v___y_2849_ = v___y_3160_;
v___y_2850_ = v___x_3170_;
v___y_2851_ = v___x_3177_;
v___y_2852_ = v___x_3174_;
v_charInst_x3f_2853_ = v_a_3189_;
v___y_2854_ = v___y_3154_;
v___y_2855_ = v___y_3145_;
v___y_2856_ = v___y_3143_;
v___y_2857_ = v___y_3146_;
v___y_2858_ = v___y_3158_;
v___y_2859_ = v___y_3142_;
v___y_2860_ = v___y_3148_;
v___y_2861_ = v___y_3159_;
v___y_2862_ = v___y_3152_;
v___y_2863_ = v___y_3151_;
goto v___jp_2831_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3186_);
lean_dec(v_a_3184_);
lean_dec(v_a_3182_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3167_);
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3188_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3188_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
lean_dec(v_a_3179_);
v_a_3198_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3199_ = lean_box(0);
v___y_2832_ = v___y_3141_;
v___y_2833_ = v___x_3169_;
v___y_2834_ = v___x_3168_;
v___y_2835_ = v___y_3144_;
v___y_2836_ = v_a_3182_;
v___y_2837_ = v___y_3147_;
v___y_2838_ = v___y_3161_;
v___y_2839_ = v___y_3149_;
v___y_2840_ = v___y_3150_;
v___y_2841_ = v___x_3173_;
v___y_2842_ = v_a_3167_;
v___y_2843_ = v___y_3153_;
v___y_2844_ = v_a_3198_;
v___y_2845_ = v___y_3155_;
v___y_2846_ = v_a_3184_;
v___y_2847_ = v___y_3156_;
v___y_2848_ = v___y_3157_;
v___y_2849_ = v___y_3160_;
v___y_2850_ = v___x_3170_;
v___y_2851_ = v___x_3177_;
v___y_2852_ = v___x_3174_;
v_charInst_x3f_2853_ = v___x_3199_;
v___y_2854_ = v___y_3154_;
v___y_2855_ = v___y_3145_;
v___y_2856_ = v___y_3143_;
v___y_2857_ = v___y_3146_;
v___y_2858_ = v___y_3158_;
v___y_2859_ = v___y_3142_;
v___y_2860_ = v___y_3148_;
v___y_2861_ = v___y_3159_;
v___y_2862_ = v___y_3152_;
v___y_2863_ = v___y_3151_;
goto v___jp_2831_;
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_a_3184_);
lean_dec(v_a_3182_);
lean_dec(v_a_3179_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3167_);
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3200_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3185_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3185_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_a_3182_);
lean_dec(v_a_3179_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3167_);
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3208_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3183_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3183_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_a_3179_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3167_);
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3216_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3181_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3181_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3173_);
lean_dec(v_a_3167_);
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3224_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3178_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3178_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3232_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3166_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3166_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v___y_3160_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
lean_dec(v___y_3144_);
lean_dec(v___y_3141_);
lean_dec(v_a_3139_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3240_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3163_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3163_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_a_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3465_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3138_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3138_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_a_3135_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3473_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3136_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3136_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3481_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3134_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3134_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
v___jp_2623_:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2649_, v___y_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_structs_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v_structs_2661_ = lean_ctor_get(v_a_2660_, 0);
lean_inc_ref(v_structs_2661_);
lean_dec(v_a_2660_);
v___x_2662_ = lean_array_get_size(v_structs_2661_);
lean_dec_ref(v_structs_2661_);
v___x_2663_ = lean_unsigned_to_nat(32u);
v___x_2664_ = lean_mk_empty_array_with_capacity(v___x_2663_);
v___x_2665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2666_ = ((size_t)5ULL);
lean_inc(v___y_2634_);
v___x_2667_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2664_);
lean_ctor_set(v___x_2667_, 2, v___y_2634_);
lean_ctor_set(v___x_2667_, 3, v___y_2634_);
lean_ctor_set_usize(v___x_2667_, 4, v___x_2666_);
v___x_2668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2669_ = lean_box(0);
v___x_2670_ = lean_box(0);
lean_inc_ref_n(v___x_2667_, 7);
lean_inc(v___y_2638_);
lean_inc(v___y_2625_);
lean_inc(v___y_2629_);
lean_inc(v___y_2637_);
lean_inc(v___y_2627_);
v___x_2671_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2671_, 0, v___x_2662_);
lean_ctor_set(v___x_2671_, 1, v_a_2611_);
lean_ctor_set(v___x_2671_, 2, v_type_2523_);
lean_ctor_set(v___x_2671_, 3, v_val_2606_);
lean_ctor_set(v___x_2671_, 4, v___y_2636_);
lean_ctor_set(v___x_2671_, 5, v_a_2617_);
lean_ctor_set(v___x_2671_, 6, v_a_2620_);
lean_ctor_set(v___x_2671_, 7, v_a_2622_);
lean_ctor_set(v___x_2671_, 8, v___y_2633_);
lean_ctor_set(v___x_2671_, 9, v___y_2642_);
lean_ctor_set(v___x_2671_, 10, v___y_2635_);
lean_ctor_set(v___x_2671_, 11, v___y_2647_);
lean_ctor_set(v___x_2671_, 12, v___y_2627_);
lean_ctor_set(v___x_2671_, 13, v___y_2639_);
lean_ctor_set(v___x_2671_, 14, v___y_2637_);
lean_ctor_set(v___x_2671_, 15, v___y_2629_);
lean_ctor_set(v___x_2671_, 16, v___y_2625_);
lean_ctor_set(v___x_2671_, 17, v___y_2641_);
lean_ctor_set(v___x_2671_, 18, v___y_2643_);
lean_ctor_set(v___x_2671_, 19, v___y_2638_);
lean_ctor_set(v___x_2671_, 20, v___y_2624_);
lean_ctor_set(v___x_2671_, 21, v___y_2644_);
lean_ctor_set(v___x_2671_, 22, v___y_2632_);
lean_ctor_set(v___x_2671_, 23, v___y_2628_);
lean_ctor_set(v___x_2671_, 24, v___y_2645_);
lean_ctor_set(v___x_2671_, 25, v___y_2631_);
lean_ctor_set(v___x_2671_, 26, v___y_2646_);
lean_ctor_set(v___x_2671_, 27, v_homomulFn_x3f_2648_);
lean_ctor_set(v___x_2671_, 28, v___y_2626_);
lean_ctor_set(v___x_2671_, 29, v___y_2640_);
lean_ctor_set(v___x_2671_, 30, v___x_2667_);
lean_ctor_set(v___x_2671_, 31, v___x_2668_);
lean_ctor_set(v___x_2671_, 32, v___x_2667_);
lean_ctor_set(v___x_2671_, 33, v___x_2667_);
lean_ctor_set(v___x_2671_, 34, v___x_2667_);
lean_ctor_set(v___x_2671_, 35, v___x_2667_);
lean_ctor_set(v___x_2671_, 36, v___x_2669_);
lean_ctor_set(v___x_2671_, 37, v___x_2668_);
lean_ctor_set(v___x_2671_, 38, v___x_2667_);
lean_ctor_set(v___x_2671_, 39, v___x_2670_);
lean_ctor_set(v___x_2671_, 40, v___x_2667_);
lean_ctor_set(v___x_2671_, 41, v___x_2667_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*42, v___y_2630_);
v___f_2672_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2672_, 0, v___x_2671_);
v___x_2673_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2674_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2673_, v___f_2672_, v___y_2649_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref_known(v___x_2674_, 1);
if (lean_obj_tag(v___y_2638_) == 1)
{
if (lean_obj_tag(v___y_2627_) == 0)
{
lean_dec_ref_known(v___y_2638_, 1);
lean_dec(v___y_2637_);
lean_dec(v___y_2629_);
lean_dec(v___y_2625_);
v___y_2536_ = v___x_2662_;
goto v___jp_2535_;
}
else
{
lean_dec_ref_known(v___y_2627_, 1);
if (lean_obj_tag(v___y_2637_) == 0)
{
if (v___y_2630_ == 0)
{
if (lean_obj_tag(v___y_2629_) == 0)
{
lean_object* v_val_2675_; uint8_t v___x_2676_; 
v_val_2675_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v___y_2638_, 1);
v___x_2676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2625_);
lean_dec(v___y_2625_);
if (v___x_2676_ == 0)
{
lean_dec(v_val_2675_);
v___y_2536_ = v___x_2662_;
goto v___jp_2535_;
}
else
{
v___y_2551_ = v___y_2649_;
v___y_2552_ = v___y_2652_;
v___y_2553_ = v___y_2651_;
v___y_2554_ = v___y_2658_;
v___y_2555_ = v_val_2675_;
v___y_2556_ = v___y_2654_;
v___y_2557_ = v___y_2655_;
v___y_2558_ = v___y_2656_;
v___y_2559_ = v___y_2650_;
v___y_2560_ = v___y_2630_;
v___y_2561_ = v___y_2653_;
v___y_2562_ = v___x_2662_;
v___y_2563_ = v___y_2657_;
goto v___jp_2550_;
}
}
else
{
lean_object* v_val_2677_; 
lean_dec_ref_known(v___y_2629_, 1);
lean_dec(v___y_2625_);
v_val_2677_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v___y_2638_, 1);
v___y_2551_ = v___y_2649_;
v___y_2552_ = v___y_2652_;
v___y_2553_ = v___y_2651_;
v___y_2554_ = v___y_2658_;
v___y_2555_ = v_val_2677_;
v___y_2556_ = v___y_2654_;
v___y_2557_ = v___y_2655_;
v___y_2558_ = v___y_2656_;
v___y_2559_ = v___y_2650_;
v___y_2560_ = v___y_2630_;
v___y_2561_ = v___y_2653_;
v___y_2562_ = v___x_2662_;
v___y_2563_ = v___y_2657_;
goto v___jp_2550_;
}
}
else
{
lean_object* v_val_2678_; 
lean_dec(v___y_2629_);
lean_dec(v___y_2625_);
v_val_2678_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_val_2678_);
lean_dec_ref_known(v___y_2638_, 1);
v___y_2576_ = v___y_2649_;
v___y_2577_ = v___y_2652_;
v___y_2578_ = v___y_2651_;
v___y_2579_ = v___y_2658_;
v___y_2580_ = v_val_2678_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2656_;
v___y_2584_ = v___y_2650_;
v___y_2585_ = v___y_2630_;
v___y_2586_ = v___y_2653_;
v___y_2587_ = v___x_2662_;
v___y_2588_ = v___y_2657_;
goto v___jp_2575_;
}
}
else
{
lean_object* v_val_2679_; 
lean_dec_ref_known(v___y_2637_, 1);
lean_dec(v___y_2629_);
lean_dec(v___y_2625_);
v_val_2679_ = lean_ctor_get(v___y_2638_, 0);
lean_inc(v_val_2679_);
lean_dec_ref_known(v___y_2638_, 1);
v___y_2576_ = v___y_2649_;
v___y_2577_ = v___y_2652_;
v___y_2578_ = v___y_2651_;
v___y_2579_ = v___y_2658_;
v___y_2580_ = v_val_2679_;
v___y_2581_ = v___y_2654_;
v___y_2582_ = v___y_2655_;
v___y_2583_ = v___y_2656_;
v___y_2584_ = v___y_2650_;
v___y_2585_ = v___y_2630_;
v___y_2586_ = v___y_2653_;
v___y_2587_ = v___x_2662_;
v___y_2588_ = v___y_2657_;
goto v___jp_2575_;
}
}
}
else
{
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2629_);
lean_dec(v___y_2627_);
lean_dec(v___y_2625_);
v___y_2536_ = v___x_2662_;
goto v___jp_2535_;
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2629_);
lean_dec(v___y_2627_);
lean_dec(v___y_2625_);
v_a_2680_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2674_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2674_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_homomulFn_x3f_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_dec(v_a_2611_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2688_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2659_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2659_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
v___jp_2696_:
{
lean_object* v___x_2731_; 
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2606_, v_type_2523_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2606_, v_type_2523_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2733_) == 0)
{
if (lean_obj_tag(v___y_2713_) == 0)
{
lean_object* v_a_2734_; 
lean_dec(v___y_2697_);
lean_del_object(v___x_2608_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___y_2624_ = v___y_2698_;
v___y_2625_ = v___y_2699_;
v___y_2626_ = v___y_2700_;
v___y_2627_ = v___y_2702_;
v___y_2628_ = v___y_2703_;
v___y_2629_ = v___y_2704_;
v___y_2630_ = v___y_2705_;
v___y_2631_ = v_a_2732_;
v___y_2632_ = v___y_2706_;
v___y_2633_ = v___y_2707_;
v___y_2634_ = v___y_2708_;
v___y_2635_ = v___y_2709_;
v___y_2636_ = v___y_2710_;
v___y_2637_ = v___y_2711_;
v___y_2638_ = v___y_2712_;
v___y_2639_ = v___y_2713_;
v___y_2640_ = v___y_2715_;
v___y_2641_ = v___y_2714_;
v___y_2642_ = v___y_2717_;
v___y_2643_ = v___y_2716_;
v___y_2644_ = v_ltFn_x3f_2720_;
v___y_2645_ = v___y_2718_;
v___y_2646_ = v_a_2734_;
v___y_2647_ = v___y_2719_;
v_homomulFn_x3f_2648_ = v___y_2701_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2729_;
v___y_2658_ = v___y_2730_;
goto v___jp_2623_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v___y_2701_);
v_a_2735_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2736_, v_val_2606_, v_type_2523_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2740_ = l_Lean_mkConst(v___x_2739_, v___y_2697_);
lean_inc_ref_n(v_type_2523_, 3);
v___x_2741_ = l_Lean_mkApp4(v___x_2740_, v_type_2523_, v_type_2523_, v_type_2523_, v_a_2738_);
v___x_2742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2741_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_a_2743_);
v___x_2745_ = v___x_2608_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
v___y_2624_ = v___y_2698_;
v___y_2625_ = v___y_2699_;
v___y_2626_ = v___y_2700_;
v___y_2627_ = v___y_2702_;
v___y_2628_ = v___y_2703_;
v___y_2629_ = v___y_2704_;
v___y_2630_ = v___y_2705_;
v___y_2631_ = v_a_2732_;
v___y_2632_ = v___y_2706_;
v___y_2633_ = v___y_2707_;
v___y_2634_ = v___y_2708_;
v___y_2635_ = v___y_2709_;
v___y_2636_ = v___y_2710_;
v___y_2637_ = v___y_2711_;
v___y_2638_ = v___y_2712_;
v___y_2639_ = v___y_2713_;
v___y_2640_ = v___y_2715_;
v___y_2641_ = v___y_2714_;
v___y_2642_ = v___y_2717_;
v___y_2643_ = v___y_2716_;
v___y_2644_ = v_ltFn_x3f_2720_;
v___y_2645_ = v___y_2718_;
v___y_2646_ = v_a_2735_;
v___y_2647_ = v___y_2719_;
v_homomulFn_x3f_2648_ = v___x_2745_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
v___y_2655_ = v___y_2727_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2729_;
v___y_2658_ = v___y_2730_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec_ref_known(v___y_2713_, 1);
lean_dec(v_a_2735_);
lean_dec(v_a_2732_);
lean_dec(v_ltFn_x3f_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2747_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2742_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref_known(v___y_2713_, 1);
lean_dec(v_a_2735_);
lean_dec(v_a_2732_);
lean_dec(v_ltFn_x3f_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2755_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2737_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2737_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2732_);
lean_dec(v_ltFn_x3f_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2763_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2733_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2733_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_ltFn_x3f_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2771_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2731_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2731_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2779_:
{
if (lean_obj_tag(v_a_2620_) == 1)
{
lean_object* v_val_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_val_2814_ = lean_ctor_get(v_a_2620_, 0);
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2816_ = l_Lean_mkConst(v___x_2815_, v___y_2787_);
lean_inc(v_val_2814_);
lean_inc_ref(v_type_2523_);
v___x_2817_ = l_Lean_mkAppB(v___x_2816_, v_type_2523_, v_val_2814_);
v___x_2818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2817_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
if (v_isShared_2614_ == 0)
{
lean_ctor_set_tag(v___x_2613_, 1);
lean_ctor_set(v___x_2613_, 0, v_a_2819_);
v___x_2821_ = v___x_2613_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
v___y_2697_ = v___y_2780_;
v___y_2698_ = v_leFn_x3f_2803_;
v___y_2699_ = v___y_2781_;
v___y_2700_ = v___y_2782_;
v___y_2701_ = v___y_2783_;
v___y_2702_ = v___y_2784_;
v___y_2703_ = v___y_2785_;
v___y_2704_ = v___y_2786_;
v___y_2705_ = v___y_2788_;
v___y_2706_ = v___y_2789_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v___y_2791_;
v___y_2709_ = v___y_2792_;
v___y_2710_ = v___y_2794_;
v___y_2711_ = v___y_2793_;
v___y_2712_ = v___y_2795_;
v___y_2713_ = v___y_2796_;
v___y_2714_ = v___y_2798_;
v___y_2715_ = v___y_2797_;
v___y_2716_ = v___y_2800_;
v___y_2717_ = v___y_2799_;
v___y_2718_ = v___y_2801_;
v___y_2719_ = v___y_2802_;
v_ltFn_x3f_2720_ = v___x_2821_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
v___y_2730_ = v___y_2813_;
goto v___jp_2696_;
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref_known(v_a_2620_, 1);
lean_dec(v_leFn_x3f_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec(v_a_2622_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2823_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2818_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2818_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_dec(v___y_2787_);
lean_del_object(v___x_2613_);
lean_inc(v___y_2783_);
v___y_2697_ = v___y_2780_;
v___y_2698_ = v_leFn_x3f_2803_;
v___y_2699_ = v___y_2781_;
v___y_2700_ = v___y_2782_;
v___y_2701_ = v___y_2783_;
v___y_2702_ = v___y_2784_;
v___y_2703_ = v___y_2785_;
v___y_2704_ = v___y_2786_;
v___y_2705_ = v___y_2788_;
v___y_2706_ = v___y_2789_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v___y_2791_;
v___y_2709_ = v___y_2792_;
v___y_2710_ = v___y_2794_;
v___y_2711_ = v___y_2793_;
v___y_2712_ = v___y_2795_;
v___y_2713_ = v___y_2796_;
v___y_2714_ = v___y_2798_;
v___y_2715_ = v___y_2797_;
v___y_2716_ = v___y_2800_;
v___y_2717_ = v___y_2799_;
v___y_2718_ = v___y_2801_;
v___y_2719_ = v___y_2802_;
v_ltFn_x3f_2720_ = v___y_2783_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
v___y_2727_ = v___y_2810_;
v___y_2728_ = v___y_2811_;
v___y_2729_ = v___y_2812_;
v___y_2730_ = v___y_2813_;
goto v___jp_2696_;
}
}
v___jp_2831_:
{
lean_object* v___x_2864_; 
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2606_, v_type_2523_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2867_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2866_, v_val_2606_, v_type_2523_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_n(v_a_2868_, 2);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2837_);
v___x_2870_ = l_Lean_mkConst(v___x_2869_, v___y_2837_);
lean_inc_ref(v_type_2523_);
v___x_2871_ = l_Lean_mkAppB(v___x_2870_, v_type_2523_, v_a_2868_);
v___x_2872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2871_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2837_);
v___x_2875_ = l_Lean_mkConst(v___x_2874_, v___y_2837_);
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2523_);
v___x_2878_ = l_Lean_mkAppB(v___x_2875_, v_type_2523_, v___x_2877_);
v___x_2879_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2878_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_3101_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_3101_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_3101_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_val_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_3096_; 
lean_del_object(v___x_2882_);
v_val_2884_ = lean_ctor_get(v_a_2880_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_a_2880_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_2886_ = v_a_2880_;
v_isShared_2887_ = v_isSharedCheck_3096_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_val_2884_);
lean_dec(v_a_2880_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_3096_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2837_);
v___x_2889_ = l_Lean_mkConst(v___x_2888_, v___y_2837_);
lean_inc_ref(v_type_2523_);
v___x_2890_ = l_Lean_mkApp3(v___x_2889_, v_type_2523_, v___x_2877_, v_val_2884_);
v___x_2891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2890_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc_n(v_a_2892_, 2);
lean_dec_ref_known(v___x_2891_, 1);
lean_inc(v_a_2873_);
v___x_2893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2873_, v_a_2892_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec_ref_known(v___x_2893_, 1);
v___x_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2895_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2894_, v_val_2606_, v_type_2523_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_n(v_a_2896_, 2);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2832_);
v___x_2898_ = l_Lean_mkConst(v___x_2897_, v___y_2832_);
lean_inc_ref_n(v_type_2523_, 3);
v___x_2899_ = l_Lean_mkApp4(v___x_2898_, v_type_2523_, v_type_2523_, v_type_2523_, v_a_2896_);
v___x_2900_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2899_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2902_, v_val_2606_, v_type_2523_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc_n(v_a_2904_, 2);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2837_);
v___x_2906_ = l_Lean_mkConst(v___x_2905_, v___y_2837_);
lean_inc_ref(v_type_2523_);
v___x_2907_ = l_Lean_mkAppB(v___x_2906_, v_type_2523_, v_a_2904_);
v___x_2908_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2907_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2606_, v_type_2523_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_n(v_a_2911_, 2);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___y_2848_);
v___x_2915_ = l_Lean_mkConst(v___x_2912_, v___x_2914_);
v___x_2916_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2523_, 2);
lean_inc_ref(v___x_2915_);
v___x_2917_ = l_Lean_mkApp4(v___x_2915_, v___x_2916_, v_type_2523_, v_type_2523_, v_a_2911_);
v___x_2918_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2917_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2606_, v_type_2523_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_n(v_a_2921_, 2);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2523_, 2);
v___x_2923_ = l_Lean_mkApp4(v___x_2915_, v___x_2922_, v_type_2523_, v_type_2523_, v_a_2921_);
v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2923_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_2927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2928_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___x_2926_, v___x_2927_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc_ref(v___y_2851_);
v___x_2929_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2868_, v___y_2851_, v___x_2928_, v_val_2606_, v_type_2523_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2929_, 1);
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2931_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___x_2926_, v___x_2930_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_2933_ = lean_box(0);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2845_, v___y_2851_, v___x_2931_, v___x_2932_, v_val_2606_, v_type_2523_, v___x_2933_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec_ref_known(v___x_2934_, 1);
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2852_);
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2936_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___y_2852_, v___x_2935_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc_ref(v___y_2841_);
v___x_2938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2896_, v___y_2841_, v___x_2936_, v___x_2937_, v_val_2606_, v_type_2523_, v___x_2933_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref_known(v___x_2938_, 1);
v___x_2939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2852_);
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2940_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___y_2852_, v___x_2939_);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
v___x_2941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2904_, v___y_2841_, v___x_2940_, v_val_2606_, v_type_2523_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_dec_ref_known(v___x_2941_, 1);
v___x_2942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2850_);
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2943_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___y_2850_, v___x_2942_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_2945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc_ref(v___y_2843_);
v___x_2946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2911_, v___y_2843_, v___x_2943_, v___x_2944_, v_val_2606_, v_type_2523_, v___x_2945_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec_ref_known(v___x_2946_, 1);
v___x_2947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2850_);
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2834_);
v___x_2948_ = l_Lean_Name_mkStr4(v___y_2834_, v___y_2833_, v___y_2850_, v___x_2947_);
v___x_2949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2523_);
lean_inc(v_val_2606_);
lean_inc_ref(v___y_2843_);
v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2921_, v___y_2843_, v___x_2948_, v___x_2944_, v_val_2606_, v_type_2523_, v___x_2949_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_dec_ref_known(v___x_2950_, 1);
if (lean_obj_tag(v_a_2617_) == 1)
{
lean_object* v_val_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_val_2951_ = lean_ctor_get(v_a_2617_, 0);
v___x_2952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2837_);
v___x_2953_ = l_Lean_mkConst(v___x_2952_, v___y_2837_);
lean_inc(v_val_2951_);
lean_inc_ref(v_type_2523_);
v___x_2954_ = l_Lean_mkAppB(v___x_2953_, v_type_2523_, v_val_2951_);
v___x_2955_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2954_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_a_2956_);
v___x_2958_ = v___x_2886_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v___y_2780_ = v___y_2832_;
v___y_2781_ = v_charInst_x3f_2853_;
v___y_2782_ = v_a_2901_;
v___y_2783_ = v___x_2933_;
v___y_2784_ = v___y_2835_;
v___y_2785_ = v_a_2919_;
v___y_2786_ = v___y_2836_;
v___y_2787_ = v___y_2837_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2839_;
v___y_2790_ = v___y_2840_;
v___y_2791_ = v___x_2876_;
v___y_2792_ = v___y_2842_;
v___y_2793_ = v___y_2844_;
v___y_2794_ = v___y_2843_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v___y_2847_;
v___y_2797_ = v_a_2909_;
v___y_2798_ = v_a_2873_;
v___y_2799_ = v___y_2849_;
v___y_2800_ = v_a_2892_;
v___y_2801_ = v_a_2925_;
v___y_2802_ = v_a_2865_;
v_leFn_x3f_2803_ = v___x_2958_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
v___y_2810_ = v___y_2860_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2862_;
v___y_2813_ = v___y_2863_;
goto v___jp_2779_;
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref_known(v_a_2617_, 1);
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec(v_a_2909_);
lean_dec(v_a_2901_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2960_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2955_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2955_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_del_object(v___x_2886_);
v___y_2780_ = v___y_2832_;
v___y_2781_ = v_charInst_x3f_2853_;
v___y_2782_ = v_a_2901_;
v___y_2783_ = v___x_2933_;
v___y_2784_ = v___y_2835_;
v___y_2785_ = v_a_2919_;
v___y_2786_ = v___y_2836_;
v___y_2787_ = v___y_2837_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2839_;
v___y_2790_ = v___y_2840_;
v___y_2791_ = v___x_2876_;
v___y_2792_ = v___y_2842_;
v___y_2793_ = v___y_2844_;
v___y_2794_ = v___y_2843_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v___y_2847_;
v___y_2797_ = v_a_2909_;
v___y_2798_ = v_a_2873_;
v___y_2799_ = v___y_2849_;
v___y_2800_ = v_a_2892_;
v___y_2801_ = v_a_2925_;
v___y_2802_ = v_a_2865_;
v_leFn_x3f_2803_ = v___x_2933_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
v___y_2810_ = v___y_2860_;
v___y_2811_ = v___y_2861_;
v___y_2812_ = v___y_2862_;
v___y_2813_ = v___y_2863_;
goto v___jp_2779_;
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2919_);
lean_dec(v_a_2909_);
lean_dec(v_a_2901_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2968_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2950_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2950_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2909_);
lean_dec(v_a_2901_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2976_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2946_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2946_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2901_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2984_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2941_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2941_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_2992_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2938_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2938_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3000_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2934_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2934_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_a_2925_);
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3008_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2929_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2929_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3016_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2924_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2924_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2915_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3024_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2920_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2920_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v___x_2915_);
lean_dec(v_a_2911_);
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3032_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2918_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2918_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec(v_a_2909_);
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3040_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2910_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2910_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_2904_);
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3048_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2908_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2908_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_a_2901_);
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3056_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2903_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2903_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_2896_);
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3064_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2900_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2900_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3072_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2895_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_2895_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_2892_);
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3080_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2893_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2893_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_del_object(v___x_2886_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3088_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_2891_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_2891_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
lean_dec(v_a_2880_);
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v___x_3097_ = lean_box(0);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_3097_);
v___x_3099_ = v___x_2882_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
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
lean_dec(v_a_2873_);
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3102_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_2879_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_2879_);
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
lean_dec(v_a_2868_);
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3110_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_2872_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_2872_);
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
lean_dec(v_a_2865_);
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3118_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2867_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_2867_);
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
lean_dec(v_charInst_x3f_2853_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2832_);
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3126_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_2864_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_2864_);
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
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_a_2620_);
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3489_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_2621_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_2621_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_a_2617_);
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3497_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_2619_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_2619_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_2613_);
lean_dec(v_a_2611_);
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
v_a_3505_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_2616_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_2616_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
else
{
lean_del_object(v___x_2608_);
lean_dec(v_val_2606_);
lean_dec_ref(v_type_2523_);
return v___x_2610_;
}
}
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
lean_dec(v_a_2602_);
lean_dec_ref(v_type_2523_);
v___x_3515_ = lean_box(0);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_3515_);
v___x_3517_ = v___x_2604_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_type_2523_);
v_a_3520_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_2601_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_2601_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
v___jp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
v___jp_2539_:
{
if (lean_obj_tag(v___y_2541_) == 0)
{
lean_dec_ref_known(v___y_2541_, 1);
v___y_2536_ = v___y_2540_;
goto v___jp_2535_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v___y_2540_);
v_a_2542_ = lean_ctor_get(v___y_2541_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___y_2541_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___y_2541_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___y_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
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
v___jp_2550_:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2555_, v___y_2560_, v___y_2562_, v___y_2551_, v___y_2559_, v___y_2553_, v___y_2552_, v___y_2561_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2563_, v___y_2554_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2565_, v___y_2562_, v___y_2551_);
v___y_2540_ = v___y_2562_;
v___y_2541_ = v___x_2566_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v___y_2562_);
v_a_2567_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2564_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2564_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
v___jp_2575_:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2580_, v___y_2585_, v___y_2587_, v___y_2576_, v___y_2584_, v___y_2578_, v___y_2577_, v___y_2586_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2588_, v___y_2579_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc_n(v_a_2590_, 2);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2590_, v___y_2587_, v___y_2576_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref_known(v___x_2591_, 1);
v___x_2592_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2590_, v___y_2587_, v___y_2576_);
v___y_2540_ = v___y_2587_;
v___y_2541_ = v___x_2592_;
goto v___jp_2539_;
}
else
{
lean_dec(v_a_2590_);
v___y_2540_ = v___y_2587_;
v___y_2541_ = v___x_2591_;
goto v___jp_2539_;
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v___y_2587_);
v_a_2593_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2589_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2589_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec(v_a_3529_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3542_, v_x_3543_, v_x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3546_, lean_object* v_x_3547_, size_t v_x_3548_, size_t v_x_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3547_, v_x_3548_, v_x_3549_, v_x_3550_, v_x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_){
_start:
{
size_t v_x_577967__boxed_3559_; size_t v_x_577968__boxed_3560_; lean_object* v_res_3561_; 
v_x_577967__boxed_3559_ = lean_unbox_usize(v_x_3555_);
lean_dec(v_x_3555_);
v_x_577968__boxed_3560_ = lean_unbox_usize(v_x_3556_);
lean_dec(v_x_3556_);
v_res_3561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3553_, v_x_3554_, v_x_577967__boxed_3559_, v_x_577968__boxed_3560_, v_x_3557_, v_x_3558_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3562_, lean_object* v_n_3563_, lean_object* v_k_3564_, lean_object* v_v_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3563_, v_k_3564_, v_v_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3567_, size_t v_depth_3568_, lean_object* v_keys_3569_, lean_object* v_vals_3570_, lean_object* v_heq_3571_, lean_object* v_i_3572_, lean_object* v_entries_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3568_, v_keys_3569_, v_vals_3570_, v_i_3572_, v_entries_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3575_, lean_object* v_depth_3576_, lean_object* v_keys_3577_, lean_object* v_vals_3578_, lean_object* v_heq_3579_, lean_object* v_i_3580_, lean_object* v_entries_3581_){
_start:
{
size_t v_depth_boxed_3582_; lean_object* v_res_3583_; 
v_depth_boxed_3582_ = lean_unbox_usize(v_depth_3576_);
lean_dec(v_depth_3576_);
v_res_3583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3575_, v_depth_boxed_3582_, v_keys_3577_, v_vals_3578_, v_heq_3579_, v_i_3580_, v_entries_3581_);
lean_dec_ref(v_vals_3578_);
lean_dec_ref(v_keys_3577_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3585_, v_x_3586_, v_x_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3590_, lean_object* v_base_3591_, lean_object* v_natModuleInst_3592_, lean_object* v_declName_3593_, lean_object* v_le_3594_, lean_object* v_mid_3595_, lean_object* v_ord_3596_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3597_ = lean_box(0);
v___x_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_val_3590_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_Lean_mkConst(v_declName_3593_, v___x_3598_);
v___x_3600_ = l_Lean_mkApp5(v___x_3599_, v_base_3591_, v_natModuleInst_3592_, v_le_3594_, v_mid_3595_, v_ord_3596_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3700_, lean_object* v_base_3701_, lean_object* v_natModuleInst_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___x_3714_; 
lean_inc_ref(v_base_3701_);
v___x_3714_ = l_Lean_Meta_getDecLevel_x3f(v_base_3701_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_4452_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_4452_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_4452_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
if (lean_obj_tag(v_a_3715_) == 1)
{
lean_object* v_val_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_4447_; 
lean_del_object(v___x_3717_);
v_val_3719_ = lean_ctor_get(v_a_3715_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_a_3715_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_3721_ = v_a_3715_;
v_isShared_3722_ = v_isSharedCheck_4447_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_val_3719_);
lean_dec(v_a_3715_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_4447_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v_a_3815_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___x_4033_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v_noNatDivInstQ_x3f_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v_isLinearInstQ_x3f_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___x_4288_; 
v___x_4033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4288_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4033_, v_val_3719_, v_base_3701_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc_n(v_a_4289_, 2);
lean_dec_ref_known(v___x_4288_, 1);
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4290_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_3719_, v_base_3701_, v_a_4289_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v_fst_4305_; lean_object* v_snd_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v_orderedAddInst_x3f_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
if (lean_obj_tag(v_a_4289_) == 1)
{
if (lean_obj_tag(v_a_4291_) == 1)
{
lean_object* v_val_4403_; lean_object* v_val_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_val_4403_ = lean_ctor_get(v_a_4289_, 0);
v_val_4404_ = lean_ctor_get(v_a_4291_, 0);
v___x_4405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4406_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4405_, v_val_3719_, v_base_3701_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4409_ = lean_box(0);
lean_inc(v_val_3719_);
v___x_4410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4410_, 0, v_val_3719_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l_Lean_mkConst(v___x_4408_, v___x_4410_);
lean_inc(v_val_4404_);
lean_inc(v_val_4403_);
lean_inc_ref(v_base_3701_);
v___x_4412_ = l_Lean_mkApp4(v___x_4411_, v_base_3701_, v_a_4407_, v_val_4403_, v_val_4404_);
v___x_4413_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4412_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v_orderedAddInst_x3f_4344_ = v_a_4414_;
v___y_4345_ = v_a_3703_;
v___y_4346_ = v_a_3704_;
v___y_4347_ = v_a_3705_;
v___y_4348_ = v_a_3706_;
v___y_4349_ = v_a_3707_;
v___y_4350_ = v_a_3708_;
v___y_4351_ = v_a_3709_;
v___y_4352_ = v_a_3710_;
v___y_4353_ = v_a_3711_;
v___y_4354_ = v_a_3712_;
goto v___jp_4343_;
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref_known(v_a_4291_, 1);
lean_dec_ref_known(v_a_4289_, 1);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4415_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4413_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4413_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec_ref_known(v_a_4291_, 1);
lean_dec_ref_known(v_a_4289_, 1);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4423_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4406_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4406_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
v___y_4392_ = v_a_3703_;
v___y_4393_ = v_a_3704_;
v___y_4394_ = v_a_3705_;
v___y_4395_ = v_a_3706_;
v___y_4396_ = v_a_3707_;
v___y_4397_ = v_a_3708_;
v___y_4398_ = v_a_3709_;
v___y_4399_ = v_a_3710_;
v___y_4400_ = v_a_3711_;
v___y_4401_ = v_a_3712_;
goto v___jp_4391_;
}
}
else
{
v___y_4392_ = v_a_3703_;
v___y_4393_ = v_a_3704_;
v___y_4394_ = v_a_3705_;
v___y_4395_ = v_a_3706_;
v___y_4396_ = v_a_3707_;
v___y_4397_ = v_a_3708_;
v___y_4398_ = v_a_3709_;
v___y_4399_ = v_a_3710_;
v___y_4400_ = v_a_3711_;
v___y_4401_ = v_a_3712_;
goto v___jp_4391_;
}
v___jp_4292_:
{
lean_object* v___x_4310_; 
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4310_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_3719_, v_base_3701_, v_a_4289_, v___y_4301_, v___y_4304_, v___y_4307_, v___y_4293_, v___y_4300_, v___y_4295_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
if (lean_obj_tag(v_a_4311_) == 0)
{
lean_dec_ref(v_snd_4306_);
lean_dec_ref(v_fst_4305_);
v___y_4215_ = v___y_4303_;
v___y_4216_ = v___y_4294_;
v___y_4217_ = v___y_4296_;
v___y_4218_ = v___y_4297_;
v___y_4219_ = v___y_4309_;
v_isLinearInstQ_x3f_4220_ = v_a_4311_;
v___y_4221_ = v___y_4302_;
v___y_4222_ = v___y_4298_;
v___y_4223_ = v___y_4308_;
v___y_4224_ = v___y_4299_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___y_4304_;
v___y_4227_ = v___y_4307_;
v___y_4228_ = v___y_4293_;
v___y_4229_ = v___y_4300_;
v___y_4230_ = v___y_4295_;
goto v___jp_4214_;
}
else
{
lean_object* v_val_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4321_; 
v_val_4312_ = lean_ctor_get(v_a_4311_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_a_4311_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4314_ = v_a_4311_;
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_val_4312_);
lean_dec(v_a_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3702_);
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3719_, v_base_3701_, v_natModuleInst_3702_, v___x_4316_, v_fst_4305_, v_val_4312_, v_snd_4306_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4317_);
v___x_4319_ = v___x_4314_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v___y_4215_ = v___y_4303_;
v___y_4216_ = v___y_4294_;
v___y_4217_ = v___y_4296_;
v___y_4218_ = v___y_4297_;
v___y_4219_ = v___y_4309_;
v_isLinearInstQ_x3f_4220_ = v___x_4319_;
v___y_4221_ = v___y_4302_;
v___y_4222_ = v___y_4298_;
v___y_4223_ = v___y_4308_;
v___y_4224_ = v___y_4299_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___y_4304_;
v___y_4227_ = v___y_4307_;
v___y_4228_ = v___y_4293_;
v___y_4229_ = v___y_4300_;
v___y_4230_ = v___y_4295_;
goto v___jp_4214_;
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v___y_4309_);
lean_dec_ref(v_snd_4306_);
lean_dec_ref(v_fst_4305_);
lean_dec(v___y_4303_);
lean_dec(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec(v___y_4294_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4322_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4310_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4310_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
v___jp_4330_:
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_box(0);
v___y_4215_ = v___x_4342_;
v___y_4216_ = v___x_4342_;
v___y_4217_ = v___x_4342_;
v___y_4218_ = v___x_4342_;
v___y_4219_ = v___x_4342_;
v_isLinearInstQ_x3f_4220_ = v___x_4342_;
v___y_4221_ = v___y_4339_;
v___y_4222_ = v___y_4334_;
v___y_4223_ = v___y_4340_;
v___y_4224_ = v___y_4336_;
v___y_4225_ = v___y_4338_;
v___y_4226_ = v___y_4332_;
v___y_4227_ = v___y_4335_;
v___y_4228_ = v___y_4331_;
v___y_4229_ = v___y_4337_;
v___y_4230_ = v___y_4333_;
goto v___jp_4214_;
}
v___jp_4343_:
{
if (lean_obj_tag(v_a_4289_) == 0)
{
lean_object* v___x_4355_; 
lean_dec(v_orderedAddInst_x3f_4344_);
lean_dec(v_a_4291_);
v___x_4355_ = lean_box(0);
v___y_4331_ = v___y_4352_;
v___y_4332_ = v___y_4350_;
v___y_4333_ = v___y_4354_;
v___y_4334_ = v___y_4346_;
v___y_4335_ = v___y_4351_;
v___y_4336_ = v___y_4348_;
v___y_4337_ = v___y_4353_;
v___y_4338_ = v___y_4349_;
v___y_4339_ = v___y_4345_;
v___y_4340_ = v___y_4347_;
v___y_4341_ = v___x_4355_;
goto v___jp_4330_;
}
else
{
if (lean_obj_tag(v_a_4291_) == 0)
{
lean_object* v___x_4356_; 
lean_dec_ref_known(v_a_4289_, 1);
lean_dec(v_orderedAddInst_x3f_4344_);
v___x_4356_ = lean_box(0);
v___y_4331_ = v___y_4352_;
v___y_4332_ = v___y_4350_;
v___y_4333_ = v___y_4354_;
v___y_4334_ = v___y_4346_;
v___y_4335_ = v___y_4351_;
v___y_4336_ = v___y_4348_;
v___y_4337_ = v___y_4353_;
v___y_4338_ = v___y_4349_;
v___y_4339_ = v___y_4345_;
v___y_4340_ = v___y_4347_;
v___y_4341_ = v___x_4356_;
goto v___jp_4330_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4344_) == 0)
{
lean_object* v___x_4357_; 
lean_dec_ref_known(v_a_4291_, 1);
lean_dec_ref_known(v_a_4289_, 1);
v___x_4357_ = lean_box(0);
v___y_4331_ = v___y_4352_;
v___y_4332_ = v___y_4350_;
v___y_4333_ = v___y_4354_;
v___y_4334_ = v___y_4346_;
v___y_4335_ = v___y_4351_;
v___y_4336_ = v___y_4348_;
v___y_4337_ = v___y_4353_;
v___y_4338_ = v___y_4349_;
v___y_4339_ = v___y_4345_;
v___y_4340_ = v___y_4347_;
v___y_4341_ = v___x_4357_;
goto v___jp_4330_;
}
else
{
lean_object* v_val_4358_; lean_object* v_val_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4390_; 
v_val_4358_ = lean_ctor_get(v_a_4289_, 0);
v_val_4359_ = lean_ctor_get(v_a_4291_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_a_4291_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4361_ = v_a_4291_;
v_isShared_4362_ = v_isSharedCheck_4390_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_val_4359_);
lean_dec(v_a_4291_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4390_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_val_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4389_; 
v_val_4363_ = lean_ctor_get(v_orderedAddInst_x3f_4344_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_orderedAddInst_x3f_4344_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4365_ = v_orderedAddInst_x3f_4344_;
v_isShared_4366_ = v_isSharedCheck_4389_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_val_4363_);
lean_dec(v_orderedAddInst_x3f_4344_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4389_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4363_);
lean_inc(v_val_4359_);
lean_inc(v_val_4358_);
lean_inc_ref(v_natModuleInst_3702_);
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3719_, v_base_3701_, v_natModuleInst_3702_, v___x_4367_, v_val_4358_, v_val_4359_, v_val_4363_);
lean_inc_ref(v___x_4368_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4368_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
v___x_4371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4363_);
lean_inc(v_val_4359_);
lean_inc(v_val_4358_);
lean_inc_ref(v_natModuleInst_3702_);
lean_inc_ref(v_base_3701_);
lean_inc(v_val_3719_);
v___x_4372_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3719_, v_base_3701_, v_natModuleInst_3702_, v___x_4371_, v_val_4358_, v_val_4359_, v_val_4363_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4372_);
v___x_4374_ = v___x_4361_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4363_, 2);
lean_inc(v_val_4359_);
lean_inc_n(v_val_4358_, 3);
lean_inc_ref_n(v_natModuleInst_3702_, 2);
lean_inc_ref_n(v_base_3701_, 2);
lean_inc_n(v_val_3719_, 3);
v___x_4376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3719_, v_base_3701_, v_natModuleInst_3702_, v___x_4375_, v_val_4358_, v_val_4359_, v_val_4363_);
v___x_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3719_, v_base_3701_, v_natModuleInst_3702_, v___x_4378_, v_val_4358_, v_val_4359_, v_val_4363_);
v___x_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
v___x_4381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4382_ = lean_box(0);
v___x_4383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4383_, 0, v_val_3719_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = l_Lean_mkConst(v___x_4381_, v___x_4383_);
lean_inc_ref(v_type_3700_);
v___x_4385_ = l_Lean_mkAppB(v___x_4384_, v_type_3700_, v___x_4368_);
v___x_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
v___y_4293_ = v___y_4352_;
v___y_4294_ = v___x_4374_;
v___y_4295_ = v___y_4354_;
v___y_4296_ = v___x_4380_;
v___y_4297_ = v___x_4377_;
v___y_4298_ = v___y_4346_;
v___y_4299_ = v___y_4348_;
v___y_4300_ = v___y_4353_;
v___y_4301_ = v___y_4349_;
v___y_4302_ = v___y_4345_;
v___y_4303_ = v___x_4370_;
v___y_4304_ = v___y_4350_;
v_fst_4305_ = v_val_4358_;
v_snd_4306_ = v_val_4363_;
v___y_4307_ = v___y_4351_;
v___y_4308_ = v___y_4347_;
v___y_4309_ = v___x_4386_;
goto v___jp_4292_;
}
}
}
}
}
}
}
}
v___jp_4391_:
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_box(0);
v_orderedAddInst_x3f_4344_ = v___x_4402_;
v___y_4345_ = v___y_4392_;
v___y_4346_ = v___y_4393_;
v___y_4347_ = v___y_4394_;
v___y_4348_ = v___y_4395_;
v___y_4349_ = v___y_4396_;
v___y_4350_ = v___y_4397_;
v___y_4351_ = v___y_4398_;
v___y_4352_ = v___y_4399_;
v___y_4353_ = v___y_4400_;
v___y_4354_ = v___y_4401_;
goto v___jp_4343_;
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_a_4289_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4431_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4290_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4290_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4439_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4288_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4288_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
v___jp_3723_:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3732_, v___y_3731_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v_structs_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
v_structs_3746_ = lean_ctor_get(v_a_3745_, 0);
lean_inc_ref(v_structs_3746_);
lean_dec(v_a_3745_);
v___x_3747_ = lean_array_get_size(v_structs_3746_);
lean_dec_ref(v_structs_3746_);
v___x_3748_ = lean_box(0);
lean_inc_ref(v___y_3741_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___y_3741_);
v___x_3750_ = v___x_3721_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___y_3741_);
v___x_3750_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; size_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___f_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_inc_ref(v___y_3739_);
v___x_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___y_3739_);
v___x_3752_ = lean_unsigned_to_nat(32u);
v___x_3753_ = lean_mk_empty_array_with_capacity(v___x_3752_);
v___x_3754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3755_ = ((size_t)5ULL);
lean_inc(v___y_3742_);
v___x_3756_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3753_);
lean_ctor_set(v___x_3756_, 2, v___y_3742_);
lean_ctor_set(v___x_3756_, 3, v___y_3742_);
lean_ctor_set_usize(v___x_3756_, 4, v___x_3755_);
v___x_3757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3758_ = 0;
v___x_3759_ = lean_box(0);
lean_inc_ref_n(v___x_3756_, 7);
v___x_3760_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3760_, 0, v___x_3747_);
lean_ctor_set(v___x_3760_, 1, v___x_3748_);
lean_ctor_set(v___x_3760_, 2, v_type_3700_);
lean_ctor_set(v___x_3760_, 3, v_val_3719_);
lean_ctor_set(v___x_3760_, 4, v___y_3724_);
lean_ctor_set(v___x_3760_, 5, v___y_3735_);
lean_ctor_set(v___x_3760_, 6, v___y_3725_);
lean_ctor_set(v___x_3760_, 7, v___y_3738_);
lean_ctor_set(v___x_3760_, 8, v___y_3729_);
lean_ctor_set(v___x_3760_, 9, v___y_3727_);
lean_ctor_set(v___x_3760_, 10, v___y_3730_);
lean_ctor_set(v___x_3760_, 11, v___y_3733_);
lean_ctor_set(v___x_3760_, 12, v___x_3748_);
lean_ctor_set(v___x_3760_, 13, v___x_3748_);
lean_ctor_set(v___x_3760_, 14, v___x_3748_);
lean_ctor_set(v___x_3760_, 15, v___x_3748_);
lean_ctor_set(v___x_3760_, 16, v___x_3748_);
lean_ctor_set(v___x_3760_, 17, v___y_3734_);
lean_ctor_set(v___x_3760_, 18, v___y_3737_);
lean_ctor_set(v___x_3760_, 19, v___x_3748_);
lean_ctor_set(v___x_3760_, 20, v___y_3726_);
lean_ctor_set(v___x_3760_, 21, v_a_3743_);
lean_ctor_set(v___x_3760_, 22, v___y_3740_);
lean_ctor_set(v___x_3760_, 23, v___y_3741_);
lean_ctor_set(v___x_3760_, 24, v___y_3739_);
lean_ctor_set(v___x_3760_, 25, v___x_3750_);
lean_ctor_set(v___x_3760_, 26, v___x_3751_);
lean_ctor_set(v___x_3760_, 27, v___x_3748_);
lean_ctor_set(v___x_3760_, 28, v___y_3736_);
lean_ctor_set(v___x_3760_, 29, v___y_3728_);
lean_ctor_set(v___x_3760_, 30, v___x_3756_);
lean_ctor_set(v___x_3760_, 31, v___x_3757_);
lean_ctor_set(v___x_3760_, 32, v___x_3756_);
lean_ctor_set(v___x_3760_, 33, v___x_3756_);
lean_ctor_set(v___x_3760_, 34, v___x_3756_);
lean_ctor_set(v___x_3760_, 35, v___x_3756_);
lean_ctor_set(v___x_3760_, 36, v___x_3748_);
lean_ctor_set(v___x_3760_, 37, v___x_3757_);
lean_ctor_set(v___x_3760_, 38, v___x_3756_);
lean_ctor_set(v___x_3760_, 39, v___x_3759_);
lean_ctor_set(v___x_3760_, 40, v___x_3756_);
lean_ctor_set(v___x_3760_, 41, v___x_3756_);
lean_ctor_set_uint8(v___x_3760_, sizeof(void*)*42, v___x_3758_);
v___f_3761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_3761_, 0, v___x_3760_);
v___x_3762_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3763_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3762_, v___f_3761_, v___y_3732_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3771_; 
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___x_3763_, 0);
lean_dec(v_unused_3772_);
v___x_3765_ = v___x_3763_;
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
else
{
lean_dec(v___x_3763_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3747_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3763_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3763_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v_a_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3782_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3744_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3744_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
v___jp_3790_:
{
if (lean_obj_tag(v___y_3792_) == 0)
{
lean_dec(v___y_3797_);
v___y_3724_ = v___y_3791_;
v___y_3725_ = v___y_3792_;
v___y_3726_ = v_a_3815_;
v___y_3727_ = v___y_3793_;
v___y_3728_ = v___y_3794_;
v___y_3729_ = v___y_3795_;
v___y_3730_ = v___y_3796_;
v___y_3731_ = v___y_3798_;
v___y_3732_ = v___y_3800_;
v___y_3733_ = v___y_3801_;
v___y_3734_ = v___y_3802_;
v___y_3735_ = v___y_3803_;
v___y_3736_ = v___y_3804_;
v___y_3737_ = v___y_3806_;
v___y_3738_ = v___y_3807_;
v___y_3739_ = v___y_3809_;
v___y_3740_ = v___y_3812_;
v___y_3741_ = v___y_3811_;
v___y_3742_ = v___y_3810_;
v_a_3743_ = v___y_3792_;
goto v___jp_3723_;
}
else
{
lean_object* v_val_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_val_3816_ = lean_ctor_get(v___y_3792_, 0);
v___x_3817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3818_ = l_Lean_mkConst(v___x_3817_, v___y_3797_);
lean_inc(v_val_3816_);
lean_inc_ref(v_type_3700_);
v___x_3819_ = l_Lean_mkAppB(v___x_3818_, v_type_3700_, v_val_3816_);
v___x_3820_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3819_, v___y_3813_, v___y_3799_, v___y_3805_, v___y_3814_, v___y_3798_, v___y_3808_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3822_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_a_3821_);
v___y_3724_ = v___y_3791_;
v___y_3725_ = v___y_3792_;
v___y_3726_ = v_a_3815_;
v___y_3727_ = v___y_3793_;
v___y_3728_ = v___y_3794_;
v___y_3729_ = v___y_3795_;
v___y_3730_ = v___y_3796_;
v___y_3731_ = v___y_3798_;
v___y_3732_ = v___y_3800_;
v___y_3733_ = v___y_3801_;
v___y_3734_ = v___y_3802_;
v___y_3735_ = v___y_3803_;
v___y_3736_ = v___y_3804_;
v___y_3737_ = v___y_3806_;
v___y_3738_ = v___y_3807_;
v___y_3739_ = v___y_3809_;
v___y_3740_ = v___y_3812_;
v___y_3741_ = v___y_3811_;
v___y_3742_ = v___y_3810_;
v_a_3743_ = v___x_3822_;
goto v___jp_3723_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref_known(v___y_3792_, 1);
lean_dec(v_a_3815_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3791_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3823_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3820_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3820_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
v___jp_3831_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3836_);
v___x_3871_ = l_Lean_Name_mkStr2(v___y_3836_, v___x_3870_);
lean_inc(v___y_3840_);
v___x_3872_ = l_Lean_mkConst(v___x_3871_, v___y_3840_);
lean_inc_ref(v_type_3700_);
v___x_3873_ = l_Lean_mkAppB(v___x_3872_, v_type_3700_, v___y_3847_);
v___x_3874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3873_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3843_);
v___x_3877_ = l_Lean_Name_mkStr2(v___y_3843_, v___x_3876_);
lean_inc(v___y_3840_);
v___x_3878_ = l_Lean_mkConst(v___x_3877_, v___y_3840_);
lean_inc_ref(v_type_3700_);
v___x_3879_ = l_Lean_mkApp3(v___x_3878_, v_type_3700_, v___y_3857_, v___y_3835_);
v___x_3880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3879_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3852_);
v___x_3883_ = l_Lean_Name_mkStr2(v___y_3852_, v___x_3882_);
lean_inc(v___y_3846_);
v___x_3884_ = l_Lean_mkConst(v___x_3883_, v___y_3846_);
lean_inc_ref_n(v_type_3700_, 3);
v___x_3885_ = l_Lean_mkApp4(v___x_3884_, v_type_3700_, v_type_3700_, v_type_3700_, v___y_3856_);
v___x_3886_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3885_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3855_);
v___x_3889_ = l_Lean_Name_mkStr2(v___y_3855_, v___x_3888_);
v___x_3890_ = l_Lean_mkConst(v___x_3889_, v___y_3846_);
lean_inc_ref_n(v_type_3700_, 3);
v___x_3891_ = l_Lean_mkApp4(v___x_3890_, v_type_3700_, v_type_3700_, v_type_3700_, v___y_3859_);
v___x_3892_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3891_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3833_);
v___x_3895_ = l_Lean_Name_mkStr2(v___y_3833_, v___x_3894_);
lean_inc(v___y_3840_);
v___x_3896_ = l_Lean_mkConst(v___x_3895_, v___y_3840_);
lean_inc_ref(v_type_3700_);
v___x_3897_ = l_Lean_mkAppB(v___x_3896_, v_type_3700_, v___y_3848_);
v___x_3898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3897_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3853_);
v___x_3901_ = l_Lean_Name_mkStr2(v___y_3853_, v___x_3900_);
v___x_3902_ = l_Lean_mkConst(v___x_3901_, v___y_3851_);
lean_inc_ref_n(v_type_3700_, 2);
lean_inc_ref(v___x_3902_);
v___x_3903_ = l_Lean_mkApp4(v___x_3902_, v___y_3838_, v_type_3700_, v_type_3700_, v___y_3837_);
v___x_3904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3903_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
lean_inc_ref_n(v_type_3700_, 2);
v___x_3906_ = l_Lean_mkApp4(v___x_3902_, v___y_3841_, v_type_3700_, v_type_3700_, v___y_3842_);
v___x_3907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3906_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3907_) == 0)
{
if (lean_obj_tag(v___y_3850_) == 0)
{
lean_object* v_a_3908_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___y_3791_ = v___y_3844_;
v___y_3792_ = v___y_3832_;
v___y_3793_ = v___y_3834_;
v___y_3794_ = v_a_3899_;
v___y_3795_ = v___y_3845_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3840_;
v___y_3798_ = v___y_3868_;
v___y_3799_ = v___y_3865_;
v___y_3800_ = v___y_3860_;
v___y_3801_ = v___y_3849_;
v___y_3802_ = v_a_3875_;
v___y_3803_ = v___y_3850_;
v___y_3804_ = v_a_3893_;
v___y_3805_ = v___y_3866_;
v___y_3806_ = v_a_3881_;
v___y_3807_ = v___y_3854_;
v___y_3808_ = v___y_3869_;
v___y_3809_ = v_a_3908_;
v___y_3810_ = v___y_3858_;
v___y_3811_ = v_a_3905_;
v___y_3812_ = v_a_3887_;
v___y_3813_ = v___y_3864_;
v___y_3814_ = v___y_3867_;
v_a_3815_ = v___y_3850_;
goto v___jp_3790_;
}
else
{
lean_object* v_a_3909_; lean_object* v_val_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3909_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3907_, 1);
v_val_3910_ = lean_ctor_get(v___y_3850_, 0);
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3840_);
v___x_3912_ = l_Lean_mkConst(v___x_3911_, v___y_3840_);
lean_inc(v_val_3910_);
lean_inc_ref(v_type_3700_);
v___x_3913_ = l_Lean_mkAppB(v___x_3912_, v_type_3700_, v_val_3910_);
v___x_3914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3913_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_a_3915_);
v___y_3791_ = v___y_3844_;
v___y_3792_ = v___y_3832_;
v___y_3793_ = v___y_3834_;
v___y_3794_ = v_a_3899_;
v___y_3795_ = v___y_3845_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3840_;
v___y_3798_ = v___y_3868_;
v___y_3799_ = v___y_3865_;
v___y_3800_ = v___y_3860_;
v___y_3801_ = v___y_3849_;
v___y_3802_ = v_a_3875_;
v___y_3803_ = v___y_3850_;
v___y_3804_ = v_a_3893_;
v___y_3805_ = v___y_3866_;
v___y_3806_ = v_a_3881_;
v___y_3807_ = v___y_3854_;
v___y_3808_ = v___y_3869_;
v___y_3809_ = v_a_3909_;
v___y_3810_ = v___y_3858_;
v___y_3811_ = v_a_3905_;
v___y_3812_ = v_a_3887_;
v___y_3813_ = v___y_3864_;
v___y_3814_ = v___y_3867_;
v_a_3815_ = v___x_3916_;
goto v___jp_3790_;
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_a_3909_);
lean_dec_ref_known(v___y_3850_, 1);
lean_dec(v_a_3905_);
lean_dec(v_a_3899_);
lean_dec(v_a_3893_);
lean_dec(v_a_3887_);
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3849_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3917_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3914_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3914_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_a_3905_);
lean_dec(v_a_3899_);
lean_dec(v_a_3893_);
lean_dec(v_a_3887_);
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3925_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3907_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3907_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v___x_3902_);
lean_dec(v_a_3899_);
lean_dec(v_a_3893_);
lean_dec(v_a_3887_);
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3933_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3904_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3904_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_a_3893_);
lean_dec(v_a_3887_);
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3941_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3898_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3898_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v_a_3887_);
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3949_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3892_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3892_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3881_);
lean_dec(v_a_3875_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v___y_3854_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3957_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3886_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3886_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_a_3875_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3854_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3965_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3880_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3880_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3854_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec(v___y_3832_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_3973_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3874_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3874_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
v___jp_3981_:
{
if (lean_obj_tag(v___y_3982_) == 1)
{
lean_object* v_val_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_val_4020_ = lean_ctor_get(v___y_3982_, 0);
v___x_4021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_3990_);
v___x_4022_ = l_Lean_mkConst(v___x_4021_, v___y_3990_);
lean_inc_ref(v_type_3700_);
v___x_4023_ = l_Lean_Expr_app___override(v___x_4022_, v_type_3700_);
lean_inc(v_val_4020_);
v___x_4024_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4023_, v_val_4020_, v___y_4015_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_dec_ref_known(v___x_4024_, 1);
v___y_3832_ = v___y_3982_;
v___y_3833_ = v___y_3983_;
v___y_3834_ = v___y_3984_;
v___y_3835_ = v___y_3987_;
v___y_3836_ = v___y_3986_;
v___y_3837_ = v___y_3985_;
v___y_3838_ = v___y_3989_;
v___y_3839_ = v___y_3988_;
v___y_3840_ = v___y_3990_;
v___y_3841_ = v___y_3992_;
v___y_3842_ = v___y_3991_;
v___y_3843_ = v___y_3994_;
v___y_3844_ = v___y_3993_;
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
v___y_3869_ = v___y_4019_;
goto v___jp_3831_;
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref_known(v___y_3982_, 1);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
v___y_3832_ = v___y_3982_;
v___y_3833_ = v___y_3983_;
v___y_3834_ = v___y_3984_;
v___y_3835_ = v___y_3987_;
v___y_3836_ = v___y_3986_;
v___y_3837_ = v___y_3985_;
v___y_3838_ = v___y_3989_;
v___y_3839_ = v___y_3988_;
v___y_3840_ = v___y_3990_;
v___y_3841_ = v___y_3992_;
v___y_3842_ = v___y_3991_;
v___y_3843_ = v___y_3994_;
v___y_3844_ = v___y_3993_;
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
v___y_3869_ = v___y_4019_;
goto v___jp_3831_;
}
}
v___jp_4034_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4041_, 14);
v___x_4054_ = l_Lean_mkConst(v___x_4053_, v___y_4041_);
v___x_4055_ = l_Lean_mkAppB(v___x_4054_, v_base_3701_, v_natModuleInst_3702_);
v___x_4056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4057_ = l_Lean_mkConst(v___x_4056_, v___y_4041_);
lean_inc_ref_n(v___x_4055_, 4);
lean_inc_ref_n(v_type_3700_, 14);
v___x_4058_ = l_Lean_mkAppB(v___x_4057_, v_type_3700_, v___x_4055_);
v___x_4059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4060_ = l_Lean_mkConst(v___x_4059_, v___y_4041_);
lean_inc_ref_n(v___x_4058_, 2);
v___x_4061_ = l_Lean_mkAppB(v___x_4060_, v_type_3700_, v___x_4058_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4063_ = l_Lean_mkConst(v___x_4062_, v___y_4041_);
lean_inc_ref(v___x_4061_);
v___x_4064_ = l_Lean_mkAppB(v___x_4063_, v_type_3700_, v___x_4061_);
v___x_4065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4067_ = l_Lean_mkConst(v___x_4066_, v___y_4041_);
lean_inc_ref(v___x_4064_);
v___x_4068_ = l_Lean_mkAppB(v___x_4067_, v_type_3700_, v___x_4064_);
v___x_4069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4070_ = l_Lean_mkConst(v___x_4069_, v___y_4041_);
v___x_4071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4072_ = l_Lean_mkConst(v___x_4071_, v___y_4041_);
v___x_4073_ = l_Lean_mkAppB(v___x_4072_, v_type_3700_, v___x_4061_);
v___x_4074_ = l_Lean_mkAppB(v___x_4070_, v_type_3700_, v___x_4073_);
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4076_ = l_Lean_mkConst(v___x_4075_, v___y_4041_);
v___x_4077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4078_ = l_Lean_mkConst(v___x_4077_, v___y_4041_);
v___x_4079_ = l_Lean_mkAppB(v___x_4078_, v_type_3700_, v___x_4058_);
v___x_4080_ = l_Lean_mkAppB(v___x_4076_, v_type_3700_, v___x_4079_);
v___x_4081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4082_ = l_Lean_mkConst(v___x_4081_, v___y_4041_);
v___x_4083_ = l_Lean_mkAppB(v___x_4082_, v_type_3700_, v___x_4058_);
v___x_4084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4085_ = lean_unsigned_to_nat(0u);
v___x_4086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v___y_4041_);
v___x_4088_ = l_Lean_mkConst(v___x_4084_, v___x_4087_);
v___x_4089_ = l_Lean_Int_mkType;
v___x_4090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4091_ = l_Lean_mkConst(v___x_4090_, v___y_4041_);
v___x_4092_ = l_Lean_mkAppB(v___x_4091_, v_type_3700_, v___x_4055_);
lean_inc_ref(v___x_4088_);
v___x_4093_ = l_Lean_mkApp3(v___x_4088_, v___x_4089_, v_type_3700_, v___x_4092_);
v___x_4094_ = l_Lean_Nat_mkType;
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4096_ = l_Lean_mkConst(v___x_4095_, v___y_4041_);
v___x_4097_ = l_Lean_mkAppB(v___x_4096_, v_type_3700_, v___x_4055_);
v___x_4098_ = l_Lean_mkApp3(v___x_4088_, v___x_4094_, v_type_3700_, v___x_4097_);
v___x_4099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4100_ = l_Lean_mkConst(v___x_4099_, v___y_4041_);
v___x_4101_ = l_Lean_Expr_app___override(v___x_4100_, v_type_3700_);
v___x_4102_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4101_, v___x_4055_, v___y_4048_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4102_, 1);
v___x_4103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4041_);
v___x_4104_ = l_Lean_mkConst(v___x_4103_, v___y_4041_);
lean_inc_ref(v_type_3700_);
v___x_4105_ = l_Lean_Expr_app___override(v___x_4104_, v_type_3700_);
lean_inc_ref(v___x_4064_);
v___x_4106_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4105_, v___x_4064_, v___y_4048_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec_ref_known(v___x_4106_, 1);
v___x_4107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4041_);
v___x_4109_ = l_Lean_mkConst(v___x_4108_, v___y_4041_);
v___x_4110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3700_);
v___x_4111_ = l_Lean_mkAppB(v___x_4109_, v_type_3700_, v___x_4110_);
lean_inc_ref(v___x_4068_);
v___x_4112_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4111_, v___x_4068_, v___y_4048_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec_ref_known(v___x_4112_, 1);
v___x_4113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4041_);
lean_inc_n(v_val_3719_, 2);
v___x_4115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_val_3719_);
lean_ctor_set(v___x_4115_, 1, v___y_4041_);
lean_inc_ref(v___x_4115_);
v___x_4116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4116_, 0, v_val_3719_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
lean_inc_ref(v___x_4116_);
v___x_4117_ = l_Lean_mkConst(v___x_4114_, v___x_4116_);
lean_inc_ref_n(v_type_3700_, 3);
v___x_4118_ = l_Lean_mkApp3(v___x_4117_, v_type_3700_, v_type_3700_, v_type_3700_);
lean_inc_ref(v___x_4074_);
v___x_4119_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4118_, v___x_4074_, v___y_4048_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec_ref_known(v___x_4119_, 1);
v___x_4120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4116_);
v___x_4122_ = l_Lean_mkConst(v___x_4121_, v___x_4116_);
lean_inc_ref_n(v_type_3700_, 3);
v___x_4123_ = l_Lean_mkApp3(v___x_4122_, v_type_3700_, v_type_3700_, v_type_3700_);
lean_inc_ref(v___x_4080_);
v___x_4124_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4123_, v___x_4080_, v___y_4048_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref_known(v___x_4124_, 1);
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4041_);
v___x_4127_ = l_Lean_mkConst(v___x_4126_, v___y_4041_);
lean_inc_ref(v_type_3700_);
v___x_4128_ = l_Lean_Expr_app___override(v___x_4127_, v_type_3700_);
lean_inc_ref(v___x_4083_);
v___x_4129_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4128_, v___x_4083_, v___y_4048_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref_known(v___x_4129_, 1);
v___x_4130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4086_);
lean_ctor_set(v___x_4132_, 1, v___x_4115_);
lean_inc_ref(v___x_4132_);
v___x_4133_ = l_Lean_mkConst(v___x_4131_, v___x_4132_);
lean_inc_ref_n(v_type_3700_, 2);
lean_inc_ref(v___x_4133_);
v___x_4134_ = l_Lean_mkApp3(v___x_4133_, v___x_4089_, v_type_3700_, v_type_3700_);
lean_inc_ref(v___x_4093_);
v___x_4135_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4134_, v___x_4093_, v___y_4048_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec_ref_known(v___x_4135_, 1);
lean_inc_ref_n(v_type_3700_, 2);
v___x_4136_ = l_Lean_mkApp3(v___x_4133_, v___x_4094_, v_type_3700_, v_type_3700_);
lean_inc_ref(v___x_4098_);
v___x_4137_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4136_, v___x_4098_, v___y_4048_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_dec_ref_known(v___x_4137_, 1);
if (lean_obj_tag(v___y_4035_) == 1)
{
lean_object* v_val_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_val_4138_ = lean_ctor_get(v___y_4035_, 0);
lean_inc(v___y_4041_);
v___x_4139_ = l_Lean_mkConst(v___x_4033_, v___y_4041_);
lean_inc_ref(v_type_3700_);
v___x_4140_ = l_Lean_Expr_app___override(v___x_4139_, v_type_3700_);
lean_inc(v_val_4138_);
v___x_4141_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4140_, v_val_4138_, v___y_4048_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_dec_ref_known(v___x_4141_, 1);
v___y_3982_ = v___y_4036_;
v___y_3983_ = v___x_4125_;
v___y_3984_ = v___y_4037_;
v___y_3985_ = v___x_4093_;
v___y_3986_ = v___x_4065_;
v___y_3987_ = v___x_4068_;
v___y_3988_ = v___y_4040_;
v___y_3989_ = v___x_4089_;
v___y_3990_ = v___y_4041_;
v___y_3991_ = v___x_4098_;
v___y_3992_ = v___x_4094_;
v___y_3993_ = v___x_4055_;
v___y_3994_ = v___x_4107_;
v___y_3995_ = v___y_4038_;
v___y_3996_ = v___x_4116_;
v___y_3997_ = v___x_4064_;
v___y_3998_ = v___x_4083_;
v___y_3999_ = v_noNatDivInstQ_x3f_4042_;
v___y_4000_ = v___y_4035_;
v___y_4001_ = v___x_4132_;
v___y_4002_ = v___x_4113_;
v___y_4003_ = v___x_4130_;
v___y_4004_ = v___y_4039_;
v___y_4005_ = v___x_4120_;
v___y_4006_ = v___x_4074_;
v___y_4007_ = v___x_4110_;
v___y_4008_ = v___x_4085_;
v___y_4009_ = v___x_4080_;
v___y_4010_ = v___y_4043_;
v___y_4011_ = v___y_4044_;
v___y_4012_ = v___y_4045_;
v___y_4013_ = v___y_4046_;
v___y_4014_ = v___y_4047_;
v___y_4015_ = v___y_4048_;
v___y_4016_ = v___y_4049_;
v___y_4017_ = v___y_4050_;
v___y_4018_ = v___y_4051_;
v___y_4019_ = v___y_4052_;
goto v___jp_3981_;
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref_known(v___y_4035_, 1);
lean_dec_ref_known(v___x_4132_, 2);
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
v___y_3982_ = v___y_4036_;
v___y_3983_ = v___x_4125_;
v___y_3984_ = v___y_4037_;
v___y_3985_ = v___x_4093_;
v___y_3986_ = v___x_4065_;
v___y_3987_ = v___x_4068_;
v___y_3988_ = v___y_4040_;
v___y_3989_ = v___x_4089_;
v___y_3990_ = v___y_4041_;
v___y_3991_ = v___x_4098_;
v___y_3992_ = v___x_4094_;
v___y_3993_ = v___x_4055_;
v___y_3994_ = v___x_4107_;
v___y_3995_ = v___y_4038_;
v___y_3996_ = v___x_4116_;
v___y_3997_ = v___x_4064_;
v___y_3998_ = v___x_4083_;
v___y_3999_ = v_noNatDivInstQ_x3f_4042_;
v___y_4000_ = v___y_4035_;
v___y_4001_ = v___x_4132_;
v___y_4002_ = v___x_4113_;
v___y_4003_ = v___x_4130_;
v___y_4004_ = v___y_4039_;
v___y_4005_ = v___x_4120_;
v___y_4006_ = v___x_4074_;
v___y_4007_ = v___x_4110_;
v___y_4008_ = v___x_4085_;
v___y_4009_ = v___x_4080_;
v___y_4010_ = v___y_4043_;
v___y_4011_ = v___y_4044_;
v___y_4012_ = v___y_4045_;
v___y_4013_ = v___y_4046_;
v___y_4014_ = v___y_4047_;
v___y_4015_ = v___y_4048_;
v___y_4016_ = v___y_4049_;
v___y_4017_ = v___y_4050_;
v___y_4018_ = v___y_4051_;
v___y_4019_ = v___y_4052_;
goto v___jp_3981_;
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref_known(v___x_4132_, 2);
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4150_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4137_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4137_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v___x_4133_);
lean_dec_ref_known(v___x_4132_, 2);
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4158_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4135_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4135_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4166_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4129_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4129_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4174_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4124_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4124_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref_known(v___x_4116_, 2);
lean_dec_ref_known(v___x_4115_, 2);
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4182_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4119_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4119_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4190_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4112_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4112_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4198_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4106_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4106_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4093_);
lean_dec_ref(v___x_4083_);
lean_dec_ref(v___x_4080_);
lean_dec_ref(v___x_4074_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4055_);
lean_dec(v_noNatDivInstQ_x3f_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_type_3700_);
v_a_4206_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4102_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4102_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
v___jp_4214_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4232_ = lean_box(0);
lean_inc(v_val_3719_);
v___x_4233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4233_, 0, v_val_3719_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
lean_inc_ref(v___x_4233_);
v___x_4234_ = l_Lean_mkConst(v___x_4231_, v___x_4233_);
lean_inc_ref(v_base_3701_);
v___x_4235_ = l_Lean_Expr_app___override(v___x_4234_, v_base_3701_);
v___x_4236_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4235_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
if (lean_obj_tag(v_a_4237_) == 1)
{
lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_val_4238_ = lean_ctor_get(v_a_4237_, 0);
lean_inc(v_val_4238_);
lean_dec_ref_known(v_a_4237_, 1);
v___x_4239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4233_);
v___x_4240_ = l_Lean_mkConst(v___x_4239_, v___x_4233_);
lean_inc_ref(v_base_3701_);
v___x_4241_ = l_Lean_mkAppB(v___x_4240_, v_base_3701_, v_val_4238_);
v___x_4242_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4241_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
if (lean_obj_tag(v_a_4243_) == 1)
{
lean_object* v_val_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_val_4244_ = lean_ctor_get(v_a_4243_, 0);
lean_inc(v_val_4244_);
lean_dec_ref_known(v_a_4243_, 1);
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4233_);
v___x_4246_ = l_Lean_mkConst(v___x_4245_, v___x_4233_);
lean_inc_ref(v_natModuleInst_3702_);
lean_inc_ref(v_base_3701_);
v___x_4247_ = l_Lean_mkAppB(v___x_4246_, v_base_3701_, v_natModuleInst_3702_);
v___x_4248_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4247_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
if (lean_obj_tag(v_a_4249_) == 1)
{
lean_object* v_val_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4260_; 
v_val_4250_ = lean_ctor_get(v_a_4249_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_a_4249_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4252_ = v_a_4249_;
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_val_4250_);
lean_dec(v_a_4249_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4233_);
v___x_4255_ = l_Lean_mkConst(v___x_4254_, v___x_4233_);
lean_inc_ref(v_natModuleInst_3702_);
lean_inc_ref(v_base_3701_);
v___x_4256_ = l_Lean_mkApp4(v___x_4255_, v_base_3701_, v_natModuleInst_3702_, v_val_4244_, v_val_4250_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4256_);
v___x_4258_ = v___x_4252_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v___y_4219_;
v___y_4040_ = v_isLinearInstQ_x3f_4220_;
v___y_4041_ = v___x_4233_;
v_noNatDivInstQ_x3f_4042_ = v___x_4258_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
v___y_4052_ = v___y_4230_;
goto v___jp_4034_;
}
}
}
else
{
lean_object* v___x_4261_; 
lean_dec(v_a_4249_);
lean_dec(v_val_4244_);
v___x_4261_ = lean_box(0);
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v___y_4219_;
v___y_4040_ = v_isLinearInstQ_x3f_4220_;
v___y_4041_ = v___x_4233_;
v_noNatDivInstQ_x3f_4042_ = v___x_4261_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
v___y_4052_ = v___y_4230_;
goto v___jp_4034_;
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec(v_val_4244_);
lean_dec_ref_known(v___x_4233_, 2);
lean_dec(v_isLinearInstQ_x3f_4220_);
lean_dec(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4262_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4248_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4248_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
else
{
lean_object* v___x_4270_; 
lean_dec(v_a_4243_);
v___x_4270_ = lean_box(0);
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v___y_4219_;
v___y_4040_ = v_isLinearInstQ_x3f_4220_;
v___y_4041_ = v___x_4233_;
v_noNatDivInstQ_x3f_4042_ = v___x_4270_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
v___y_4052_ = v___y_4230_;
goto v___jp_4034_;
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref_known(v___x_4233_, 2);
lean_dec(v_isLinearInstQ_x3f_4220_);
lean_dec(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4271_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4242_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4242_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_object* v___x_4279_; 
lean_dec(v_a_4237_);
v___x_4279_ = lean_box(0);
v___y_4035_ = v___y_4215_;
v___y_4036_ = v___y_4216_;
v___y_4037_ = v___y_4217_;
v___y_4038_ = v___y_4218_;
v___y_4039_ = v___y_4219_;
v___y_4040_ = v_isLinearInstQ_x3f_4220_;
v___y_4041_ = v___x_4233_;
v_noNatDivInstQ_x3f_4042_ = v___x_4279_;
v___y_4043_ = v___y_4221_;
v___y_4044_ = v___y_4222_;
v___y_4045_ = v___y_4223_;
v___y_4046_ = v___y_4224_;
v___y_4047_ = v___y_4225_;
v___y_4048_ = v___y_4226_;
v___y_4049_ = v___y_4227_;
v___y_4050_ = v___y_4228_;
v___y_4051_ = v___y_4229_;
v___y_4052_ = v___y_4230_;
goto v___jp_4034_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref_known(v___x_4233_, 2);
lean_dec(v_isLinearInstQ_x3f_4220_);
lean_dec(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_del_object(v___x_3721_);
lean_dec(v_val_3719_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4280_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4236_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4236_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_dec(v_a_3715_);
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v___x_4448_ = lean_box(0);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_4448_);
v___x_4450_ = v___x_3717_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec_ref(v_natModuleInst_3702_);
lean_dec_ref(v_base_3701_);
lean_dec_ref(v_type_3700_);
v_a_4453_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_3714_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_3714_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4461_, lean_object* v_base_4462_, lean_object* v_natModuleInst_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4461_, v_base_4462_, v_natModuleInst_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_);
lean_dec(v_a_4473_);
lean_dec_ref(v_a_4472_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec(v_a_4464_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4496_ = lean_unsigned_to_nat(2u);
v___x_4497_ = l_Lean_Expr_isAppOfArity(v_type_4483_, v___x_4495_, v___x_4496_);
if (v___x_4497_ == 0)
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
return v___x_4498_;
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4499_ = l_Lean_Expr_appFn_x21(v_type_4483_);
v___x_4500_ = l_Lean_Expr_appArg_x21(v___x_4499_);
lean_dec_ref(v___x_4499_);
v___x_4501_ = l_Lean_Expr_appArg_x21(v_type_4483_);
v___x_4502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4483_, v___x_4500_, v___x_4501_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_);
return v___x_4502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec(v_a_4504_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4516_, lean_object* v_a_4517_, lean_object* v_s_4518_){
_start:
{
lean_object* v_structs_4519_; lean_object* v_typeIdOf_4520_; lean_object* v_exprToStructId_4521_; lean_object* v_exprToStructIdEntries_4522_; lean_object* v_forbiddenNatModules_4523_; lean_object* v_natStructs_4524_; lean_object* v_natTypeIdOf_4525_; lean_object* v_exprToNatStructId_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4534_; 
v_structs_4519_ = lean_ctor_get(v_s_4518_, 0);
v_typeIdOf_4520_ = lean_ctor_get(v_s_4518_, 1);
v_exprToStructId_4521_ = lean_ctor_get(v_s_4518_, 2);
v_exprToStructIdEntries_4522_ = lean_ctor_get(v_s_4518_, 3);
v_forbiddenNatModules_4523_ = lean_ctor_get(v_s_4518_, 4);
v_natStructs_4524_ = lean_ctor_get(v_s_4518_, 5);
v_natTypeIdOf_4525_ = lean_ctor_get(v_s_4518_, 6);
v_exprToNatStructId_4526_ = lean_ctor_get(v_s_4518_, 7);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_s_4518_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4528_ = v_s_4518_;
v_isShared_4529_ = v_isSharedCheck_4534_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_exprToNatStructId_4526_);
lean_inc(v_natTypeIdOf_4525_);
lean_inc(v_natStructs_4524_);
lean_inc(v_forbiddenNatModules_4523_);
lean_inc(v_exprToStructIdEntries_4522_);
lean_inc(v_exprToStructId_4521_);
lean_inc(v_typeIdOf_4520_);
lean_inc(v_structs_4519_);
lean_dec(v_s_4518_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4534_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4530_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4520_, v_type_4516_, v_a_4517_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 1, v___x_4530_);
v___x_4532_ = v___x_4528_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_structs_4519_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4533_, 2, v_exprToStructId_4521_);
lean_ctor_set(v_reuseFailAlloc_4533_, 3, v_exprToStructIdEntries_4522_);
lean_ctor_set(v_reuseFailAlloc_4533_, 4, v_forbiddenNatModules_4523_);
lean_ctor_set(v_reuseFailAlloc_4533_, 5, v_natStructs_4524_);
lean_ctor_set(v_reuseFailAlloc_4533_, 6, v_natTypeIdOf_4525_);
lean_ctor_set(v_reuseFailAlloc_4533_, 7, v_exprToNatStructId_4526_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4535_, lean_object* v_vals_4536_, lean_object* v_i_4537_, lean_object* v_k_4538_){
_start:
{
lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = lean_array_get_size(v_keys_4535_);
v___x_4540_ = lean_nat_dec_lt(v_i_4537_, v___x_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_dec(v_i_4537_);
v___x_4541_ = lean_box(0);
return v___x_4541_;
}
else
{
lean_object* v_k_x27_4542_; uint8_t v___x_4543_; 
v_k_x27_4542_ = lean_array_fget_borrowed(v_keys_4535_, v_i_4537_);
v___x_4543_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_4538_, v_k_x27_4542_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = lean_unsigned_to_nat(1u);
v___x_4545_ = lean_nat_add(v_i_4537_, v___x_4544_);
lean_dec(v_i_4537_);
v_i_4537_ = v___x_4545_;
goto _start;
}
else
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_array_fget_borrowed(v_vals_4536_, v_i_4537_);
lean_dec(v_i_4537_);
lean_inc(v___x_4547_);
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4549_, lean_object* v_vals_4550_, lean_object* v_i_4551_, lean_object* v_k_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4549_, v_vals_4550_, v_i_4551_, v_k_4552_);
lean_dec_ref(v_k_4552_);
lean_dec_ref(v_vals_4550_);
lean_dec_ref(v_keys_4549_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4554_, size_t v_x_4555_, lean_object* v_x_4556_){
_start:
{
if (lean_obj_tag(v_x_4554_) == 0)
{
lean_object* v_es_4557_; lean_object* v___x_4558_; size_t v___x_4559_; size_t v___x_4560_; lean_object* v_j_4561_; lean_object* v___x_4562_; 
v_es_4557_ = lean_ctor_get(v_x_4554_, 0);
v___x_4558_ = lean_box(2);
v___x_4559_ = ((size_t)31ULL);
v___x_4560_ = lean_usize_land(v_x_4555_, v___x_4559_);
v_j_4561_ = lean_usize_to_nat(v___x_4560_);
v___x_4562_ = lean_array_get_borrowed(v___x_4558_, v_es_4557_, v_j_4561_);
lean_dec(v_j_4561_);
switch(lean_obj_tag(v___x_4562_))
{
case 0:
{
lean_object* v_key_4563_; lean_object* v_val_4564_; uint8_t v___x_4565_; 
v_key_4563_ = lean_ctor_get(v___x_4562_, 0);
v_val_4564_ = lean_ctor_get(v___x_4562_, 1);
v___x_4565_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4556_, v_key_4563_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_box(0);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; 
lean_inc(v_val_4564_);
v___x_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4567_, 0, v_val_4564_);
return v___x_4567_;
}
}
case 1:
{
lean_object* v_node_4568_; size_t v___x_4569_; size_t v___x_4570_; 
v_node_4568_ = lean_ctor_get(v___x_4562_, 0);
v___x_4569_ = ((size_t)5ULL);
v___x_4570_ = lean_usize_shift_right(v_x_4555_, v___x_4569_);
v_x_4554_ = v_node_4568_;
v_x_4555_ = v___x_4570_;
goto _start;
}
default: 
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_box(0);
return v___x_4572_;
}
}
}
else
{
lean_object* v_ks_4573_; lean_object* v_vs_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_ks_4573_ = lean_ctor_get(v_x_4554_, 0);
v_vs_4574_ = lean_ctor_get(v_x_4554_, 1);
v___x_4575_ = lean_unsigned_to_nat(0u);
v___x_4576_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4573_, v_vs_4574_, v___x_4575_, v_x_4556_);
return v___x_4576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4577_, lean_object* v_x_4578_, lean_object* v_x_4579_){
_start:
{
size_t v_x_8046__boxed_4580_; lean_object* v_res_4581_; 
v_x_8046__boxed_4580_ = lean_unbox_usize(v_x_4578_);
lean_dec(v_x_4578_);
v_res_4581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4577_, v_x_8046__boxed_4580_, v_x_4579_);
lean_dec_ref(v_x_4579_);
lean_dec_ref(v_x_4577_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4582_, lean_object* v_x_4583_){
_start:
{
uint64_t v___x_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4583_);
v___x_4585_ = lean_uint64_to_usize(v___x_4584_);
v___x_4586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4582_, v___x_4585_, v_x_4583_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4587_, lean_object* v_x_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4587_, v_x_4588_);
lean_dec_ref(v_x_4588_);
lean_dec_ref(v_x_4587_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4593_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4672_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4672_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4672_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
uint8_t v_linarith_4607_; 
v_linarith_4607_ = lean_ctor_get_uint8(v_a_4603_, sizeof(void*)*13 + 22);
lean_dec(v_a_4603_);
if (v_linarith_4607_ == 0)
{
lean_object* v___x_4608_; lean_object* v___x_4610_; 
lean_dec_ref(v_type_4590_);
v___x_4608_ = lean_box(0);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4608_);
v___x_4610_ = v___x_4605_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4608_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
else
{
lean_object* v___x_4612_; 
lean_del_object(v___x_4605_);
lean_inc_ref(v_type_4590_);
v___x_4612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4663_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4663_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4663_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
uint8_t v___x_4617_; 
v___x_4617_ = lean_unbox(v_a_4613_);
lean_dec(v_a_4613_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; 
lean_del_object(v___x_4615_);
v___x_4618_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4591_, v_a_4599_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4650_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4621_ = v___x_4618_;
v_isShared_4622_ = v_isSharedCheck_4650_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4618_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4650_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v_typeIdOf_4623_; lean_object* v___x_4624_; 
v_typeIdOf_4623_ = lean_ctor_get(v_a_4619_, 1);
lean_inc_ref(v_typeIdOf_4623_);
lean_dec(v_a_4619_);
v___x_4624_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4623_, v_type_4590_);
lean_dec_ref(v_typeIdOf_4623_);
if (lean_obj_tag(v___x_4624_) == 1)
{
lean_object* v_val_4625_; lean_object* v___x_4627_; 
lean_dec_ref(v_type_4590_);
v_val_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_val_4625_);
lean_dec_ref_known(v___x_4624_, 1);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v_val_4625_);
v___x_4627_ = v___x_4621_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_val_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
else
{
lean_object* v___x_4629_; 
lean_dec(v___x_4624_);
lean_del_object(v___x_4621_);
lean_inc_ref(v_type_4590_);
v___x_4629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___f_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc_n(v_a_4630_, 2);
lean_dec_ref_known(v___x_4629_, 1);
v___f_4631_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4631_, 0, v_type_4590_);
lean_closure_set(v___f_4631_, 1, v_a_4630_);
v___x_4632_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4633_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4632_, v___f_4631_, v_a_4591_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v___x_4633_, 0);
lean_dec(v_unused_4641_);
v___x_4635_ = v___x_4633_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_dec(v___x_4633_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v_a_4630_);
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4630_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4649_; 
lean_dec(v_a_4630_);
v_a_4642_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4644_ = v___x_4633_;
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4633_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
else
{
lean_dec_ref(v_type_4590_);
return v___x_4629_;
}
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec_ref(v_type_4590_);
v_a_4651_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4618_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4618_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4661_; 
lean_dec_ref(v_type_4590_);
v___x_4659_ = lean_box(0);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4659_);
v___x_4661_ = v___x_4615_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec_ref(v_type_4590_);
v_a_4664_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4612_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4612_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v_type_4590_);
v_a_4673_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4602_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4602_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec(v_a_4682_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4694_, lean_object* v_x_4695_, lean_object* v_x_4696_){
_start:
{
lean_object* v___x_4697_; 
v___x_4697_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4695_, v_x_4696_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4698_, lean_object* v_x_4699_, lean_object* v_x_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4698_, v_x_4699_, v_x_4700_);
lean_dec_ref(v_x_4700_);
lean_dec_ref(v_x_4699_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4702_, lean_object* v_x_4703_, size_t v_x_4704_, lean_object* v_x_4705_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4703_, v_x_4704_, v_x_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4707_, lean_object* v_x_4708_, lean_object* v_x_4709_, lean_object* v_x_4710_){
_start:
{
size_t v_x_8272__boxed_4711_; lean_object* v_res_4712_; 
v_x_8272__boxed_4711_ = lean_unbox_usize(v_x_4709_);
lean_dec(v_x_4709_);
v_res_4712_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4707_, v_x_4708_, v_x_8272__boxed_4711_, v_x_4710_);
lean_dec_ref(v_x_4710_);
lean_dec_ref(v_x_4708_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4713_, lean_object* v_keys_4714_, lean_object* v_vals_4715_, lean_object* v_heq_4716_, lean_object* v_i_4717_, lean_object* v_k_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4714_, v_vals_4715_, v_i_4717_, v_k_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4720_, lean_object* v_keys_4721_, lean_object* v_vals_4722_, lean_object* v_heq_4723_, lean_object* v_i_4724_, lean_object* v_k_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4720_, v_keys_4721_, v_vals_4722_, v_heq_4723_, v_i_4724_, v_k_4725_);
lean_dec_ref(v_k_4725_);
lean_dec_ref(v_vals_4722_);
lean_dec_ref(v_keys_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4727_, lean_object* v_type_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4737_, 0, v_u_4727_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = l_Lean_mkConst(v___x_4735_, v___x_4737_);
v___x_4739_ = l_Lean_Expr_app___override(v___x_4738_, v_type_4728_);
v___x_4740_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4739_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4741_, lean_object* v_type_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4741_, v_type_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec(v_a_4743_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4750_, lean_object* v_type_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4750_, v_type_4751_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4764_, lean_object* v_type_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4764_, v_type_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec(v_a_4766_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4778_, lean_object* v_s_4779_){
_start:
{
lean_object* v_structs_4780_; lean_object* v_typeIdOf_4781_; lean_object* v_exprToStructId_4782_; lean_object* v_exprToStructIdEntries_4783_; lean_object* v_forbiddenNatModules_4784_; lean_object* v_natStructs_4785_; lean_object* v_natTypeIdOf_4786_; lean_object* v_exprToNatStructId_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4795_; 
v_structs_4780_ = lean_ctor_get(v_s_4779_, 0);
v_typeIdOf_4781_ = lean_ctor_get(v_s_4779_, 1);
v_exprToStructId_4782_ = lean_ctor_get(v_s_4779_, 2);
v_exprToStructIdEntries_4783_ = lean_ctor_get(v_s_4779_, 3);
v_forbiddenNatModules_4784_ = lean_ctor_get(v_s_4779_, 4);
v_natStructs_4785_ = lean_ctor_get(v_s_4779_, 5);
v_natTypeIdOf_4786_ = lean_ctor_get(v_s_4779_, 6);
v_exprToNatStructId_4787_ = lean_ctor_get(v_s_4779_, 7);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_s_4779_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4789_ = v_s_4779_;
v_isShared_4790_ = v_isSharedCheck_4795_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_exprToNatStructId_4787_);
lean_inc(v_natTypeIdOf_4786_);
lean_inc(v_natStructs_4785_);
lean_inc(v_forbiddenNatModules_4784_);
lean_inc(v_exprToStructIdEntries_4783_);
lean_inc(v_exprToStructId_4782_);
lean_inc(v_typeIdOf_4781_);
lean_inc(v_structs_4780_);
lean_dec(v_s_4779_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4795_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4791_; lean_object* v___x_4793_; 
v___x_4791_ = lean_array_push(v_natStructs_4785_, v___x_4778_);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 5, v___x_4791_);
v___x_4793_ = v___x_4789_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_structs_4780_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v_typeIdOf_4781_);
lean_ctor_set(v_reuseFailAlloc_4794_, 2, v_exprToStructId_4782_);
lean_ctor_set(v_reuseFailAlloc_4794_, 3, v_exprToStructIdEntries_4783_);
lean_ctor_set(v_reuseFailAlloc_4794_, 4, v_forbiddenNatModules_4784_);
lean_ctor_set(v_reuseFailAlloc_4794_, 5, v___x_4791_);
lean_ctor_set(v_reuseFailAlloc_4794_, 6, v_natTypeIdOf_4786_);
lean_ctor_set(v_reuseFailAlloc_4794_, 7, v_exprToNatStructId_4787_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v_ref_4802_; lean_object* v___x_4803_; lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4812_; 
v_ref_4802_ = lean_ctor_get(v___y_4799_, 5);
v___x_4803_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4806_ = v___x_4803_;
v_isShared_4807_ = v_isSharedCheck_4812_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4803_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4812_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4808_; lean_object* v___x_4810_; 
lean_inc(v_ref_4802_);
v___x_4808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4808_, 0, v_ref_4802_);
lean_ctor_set(v___x_4808_, 1, v_a_4804_);
if (v_isShared_4807_ == 0)
{
lean_ctor_set_tag(v___x_4806_, 1);
lean_ctor_set(v___x_4806_, 0, v___x_4808_);
v___x_4810_ = v___x_4806_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
lean_dec(v___y_4817_);
lean_dec_ref(v___y_4816_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
return v_res_4819_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7));
v___x_4837_ = l_Lean_stringToMessageData(v___x_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v___x_4850_; 
lean_inc_ref(v_type_4838_);
v___x_4850_ = l_Lean_Meta_getDecLevel(v_type_4838_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc_n(v_a_4851_, 2);
lean_dec_ref_known(v___x_4850_, 1);
lean_inc_ref(v_type_4838_);
v___x_4852_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4851_, v_type_4838_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_5145_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_4855_ = v___x_4852_;
v_isShared_4856_ = v_isSharedCheck_5145_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4852_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_5145_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
if (lean_obj_tag(v_a_4853_) == 1)
{
lean_object* v_val_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
lean_del_object(v___x_4855_);
v_val_4857_ = lean_ctor_get(v_a_4853_, 0);
lean_inc_n(v_val_4857_, 2);
lean_dec_ref_known(v_a_4853_, 1);
v___x_4858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4859_ = lean_box(0);
lean_inc(v_a_4851_);
v___x_4860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4860_, 0, v_a_4851_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
lean_inc_ref(v___x_4860_);
v___x_4861_ = l_Lean_mkConst(v___x_4858_, v___x_4860_);
lean_inc_ref(v_type_4838_);
v___x_4862_ = l_Lean_mkAppB(v___x_4861_, v_type_4838_, v_val_4857_);
v___x_4863_ = l_Lean_Meta_Sym_canon(v___x_4862_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = l_Lean_Meta_Sym_shareCommon(v_a_4864_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4867_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc_n(v_a_4866_, 2);
lean_dec_ref_known(v___x_4865_, 1);
v___x_4867_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4866_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref_known(v___x_4867_, 1);
if (lean_obj_tag(v_a_4868_) == 1)
{
lean_object* v_val_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_5120_; 
v_val_4869_ = lean_ctor_get(v_a_4868_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_a_4868_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_4871_ = v_a_4868_;
v_isShared_4872_ = v_isSharedCheck_5120_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_val_4869_);
lean_dec(v_a_4868_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_5120_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4873_, v_a_4851_, v_type_4838_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v___x_4876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4876_, v_a_4851_, v_type_4838_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4879_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
lean_inc(v_a_4875_);
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4879_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_4851_, v_type_4838_, v_a_4875_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4879_, 1);
lean_inc(v_a_4875_);
lean_inc(v_a_4878_);
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4881_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_4851_, v_type_4838_, v_a_4878_, v_a_4875_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4883_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
lean_inc(v_a_4875_);
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4883_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_4851_, v_type_4838_, v_a_4875_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4883_, 1);
v___x_4885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4886_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4885_, v_a_4851_, v_type_4838_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc_n(v_a_4887_, 2);
lean_dec_ref_known(v___x_4886_, 1);
v___x_4888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4860_);
lean_inc_n(v_a_4851_, 2);
v___x_4889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_a_4851_);
lean_ctor_set(v___x_4889_, 1, v___x_4860_);
lean_inc_ref(v___x_4889_);
v___x_4890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4890_, 0, v_a_4851_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v___x_4891_ = l_Lean_mkConst(v___x_4888_, v___x_4890_);
lean_inc_ref_n(v_type_4838_, 3);
v___x_4892_ = l_Lean_mkApp4(v___x_4891_, v_type_4838_, v_type_4838_, v_type_4838_, v_a_4887_);
v___x_4893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4892_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v_orderedAddInst_x3f_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v___y_4906_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref_known(v___x_4893_, 1);
if (lean_obj_tag(v_a_4875_) == 1)
{
if (lean_obj_tag(v_a_4880_) == 1)
{
lean_object* v_val_5049_; lean_object* v_val_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v_val_5049_ = lean_ctor_get(v_a_4875_, 0);
v_val_5050_ = lean_ctor_get(v_a_4880_, 0);
v___x_5051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4860_);
v___x_5052_ = l_Lean_mkConst(v___x_5051_, v___x_4860_);
lean_inc(v_val_5050_);
lean_inc(v_val_5049_);
lean_inc_ref(v_type_4838_);
v___x_5053_ = l_Lean_mkApp4(v___x_5052_, v_type_4838_, v_a_4887_, v_val_5049_, v_val_5050_);
v___x_5054_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5053_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_a_5055_; 
v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5055_);
lean_dec_ref_known(v___x_5054_, 1);
v_orderedAddInst_x3f_4896_ = v_a_5055_;
v___y_4897_ = v_a_4839_;
v___y_4898_ = v_a_4840_;
v___y_4899_ = v_a_4841_;
v___y_4900_ = v_a_4842_;
v___y_4901_ = v_a_4843_;
v___y_4902_ = v_a_4844_;
v___y_4903_ = v_a_4845_;
v___y_4904_ = v_a_4846_;
v___y_4905_ = v_a_4847_;
v___y_4906_ = v_a_4848_;
goto v___jp_4895_;
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec_ref_known(v_a_4880_, 1);
lean_dec_ref_known(v_a_4875_, 1);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4878_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5056_ = lean_ctor_get(v___x_5054_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5054_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5054_);
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
lean_dec(v_a_4887_);
v___y_5038_ = v_a_4839_;
v___y_5039_ = v_a_4840_;
v___y_5040_ = v_a_4841_;
v___y_5041_ = v_a_4842_;
v___y_5042_ = v_a_4843_;
v___y_5043_ = v_a_4844_;
v___y_5044_ = v_a_4845_;
v___y_5045_ = v_a_4846_;
v___y_5046_ = v_a_4847_;
v___y_5047_ = v_a_4848_;
goto v___jp_5037_;
}
}
else
{
lean_dec(v_a_4887_);
v___y_5038_ = v_a_4839_;
v___y_5039_ = v_a_4840_;
v___y_5040_ = v_a_4841_;
v___y_5041_ = v_a_4842_;
v___y_5042_ = v_a_4843_;
v___y_5043_ = v_a_4844_;
v___y_5044_ = v_a_4845_;
v___y_5045_ = v_a_4846_;
v___y_5046_ = v_a_4847_;
v___y_5047_ = v_a_4848_;
goto v___jp_5037_;
}
v___jp_4895_:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4860_);
v___x_4908_ = l_Lean_mkConst(v___x_4907_, v___x_4860_);
lean_inc_ref(v_type_4838_);
v___x_4909_ = l_Lean_Expr_app___override(v___x_4908_, v_type_4838_);
v___x_4910_ = l_Lean_Meta_Sym_synthInstance(v___x_4909_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4860_);
v___x_4913_ = l_Lean_mkConst(v___x_4912_, v___x_4860_);
lean_inc_ref(v_type_4838_);
v___x_4914_ = l_Lean_mkAppB(v___x_4913_, v_type_4838_, v_a_4911_);
v___x_4915_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4914_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4860_);
v___x_4918_ = l_Lean_mkConst(v___x_4917_, v___x_4860_);
lean_inc(v_val_4857_);
lean_inc_ref(v_type_4838_);
v___x_4919_ = l_Lean_mkAppB(v___x_4918_, v_type_4838_, v_val_4857_);
v___x_4920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4919_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v___x_4922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4922_, v_a_4851_, v_type_4838_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
v___x_4925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_4926_ = l_Lean_mkConst(v___x_4925_, v___x_4860_);
lean_inc_ref(v_type_4838_);
v___x_4927_ = l_Lean_mkAppB(v___x_4926_, v_type_4838_, v_a_4924_);
v___x_4928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4927_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
lean_inc_ref(v_type_4838_);
lean_inc(v_a_4851_);
v___x_4930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4851_, v_type_4838_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
lean_ctor_set(v___x_4934_, 1, v___x_4889_);
v___x_4935_ = l_Lean_mkConst(v___x_4932_, v___x_4934_);
v___x_4936_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4838_, 2);
v___x_4937_ = l_Lean_mkApp4(v___x_4935_, v___x_4936_, v_type_4838_, v_type_4838_, v_a_4931_);
v___x_4938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4937_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4940_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v___x_4940_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4897_, v___y_4905_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v_natStructs_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___f_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v___x_4940_, 1);
v_natStructs_4942_ = lean_ctor_get(v_a_4941_, 5);
lean_inc_ref(v_natStructs_4942_);
lean_dec(v_a_4941_);
v___x_4943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4851_);
v___x_4944_ = l_Lean_Level_succ___override(v_a_4851_);
v___x_4945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
lean_ctor_set(v___x_4945_, 1, v___x_4859_);
v___x_4946_ = l_Lean_mkConst(v___x_4943_, v___x_4945_);
v___x_4947_ = l_Lean_Expr_app___override(v___x_4946_, v_a_4866_);
v___x_4948_ = lean_array_get_size(v_natStructs_4942_);
lean_dec_ref(v_natStructs_4942_);
v___x_4949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6);
v___x_4950_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v_val_4869_);
lean_ctor_set(v___x_4950_, 2, v_type_4838_);
lean_ctor_set(v___x_4950_, 3, v_a_4851_);
lean_ctor_set(v___x_4950_, 4, v_val_4857_);
lean_ctor_set(v___x_4950_, 5, v_a_4875_);
lean_ctor_set(v___x_4950_, 6, v_a_4878_);
lean_ctor_set(v___x_4950_, 7, v_a_4882_);
lean_ctor_set(v___x_4950_, 8, v_a_4880_);
lean_ctor_set(v___x_4950_, 9, v_orderedAddInst_x3f_4896_);
lean_ctor_set(v___x_4950_, 10, v_a_4884_);
lean_ctor_set(v___x_4950_, 11, v_a_4916_);
lean_ctor_set(v___x_4950_, 12, v___x_4947_);
lean_ctor_set(v___x_4950_, 13, v_a_4929_);
lean_ctor_set(v___x_4950_, 14, v_a_4921_);
lean_ctor_set(v___x_4950_, 15, v_a_4894_);
lean_ctor_set(v___x_4950_, 16, v_a_4939_);
lean_ctor_set(v___x_4950_, 17, v___x_4949_);
v___f_4951_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4951_, 0, v___x_4950_);
v___x_4952_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4953_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4952_, v___f_4951_, v___y_4897_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4963_; 
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4963_ == 0)
{
lean_object* v_unused_4964_; 
v_unused_4964_ = lean_ctor_get(v___x_4953_, 0);
lean_dec(v_unused_4964_);
v___x_4955_ = v___x_4953_;
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
else
{
lean_dec(v___x_4953_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4963_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4948_);
v___x_4958_ = v___x_4871_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4948_);
v___x_4958_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
lean_object* v___x_4960_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 0, v___x_4958_);
v___x_4960_ = v___x_4955_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4958_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
lean_del_object(v___x_4871_);
v_a_4965_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4953_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4953_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec(v_a_4939_);
lean_dec(v_a_4929_);
lean_dec(v_a_4921_);
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_4973_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4940_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4940_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec(v_a_4929_);
lean_dec(v_a_4921_);
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_4981_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4938_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4938_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec(v_a_4929_);
lean_dec(v_a_4921_);
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_4989_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4930_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4930_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec(v_a_4921_);
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_4997_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4928_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4928_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec(v_a_4921_);
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5005_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4923_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4923_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec(v_a_4916_);
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5013_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_4920_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4920_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5021_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4915_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4915_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec(v_orderedAddInst_x3f_4896_);
lean_dec(v_a_4894_);
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5029_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_4910_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_4910_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
v___jp_5037_:
{
lean_object* v___x_5048_; 
v___x_5048_ = lean_box(0);
v_orderedAddInst_x3f_4896_ = v___x_5048_;
v___y_4897_ = v___y_5038_;
v___y_4898_ = v___y_5039_;
v___y_4899_ = v___y_5040_;
v___y_4900_ = v___y_5041_;
v___y_4901_ = v___y_5042_;
v___y_4902_ = v___y_5043_;
v___y_4903_ = v___y_5044_;
v___y_4904_ = v___y_5045_;
v___y_4905_ = v___y_5046_;
v___y_4906_ = v___y_5047_;
goto v___jp_4895_;
}
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
lean_dec_ref_known(v___x_4889_, 2);
lean_dec(v_a_4887_);
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5064_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_4893_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_4893_);
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
lean_dec(v_a_4884_);
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5072_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_4886_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_4886_);
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
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_dec(v_a_4882_);
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5080_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_4883_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_4883_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec(v_a_4880_);
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5088_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_4881_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_4881_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_a_4878_);
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5096_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_4879_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_4879_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_a_4875_);
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5104_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_4877_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_4877_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_del_object(v___x_4871_);
lean_dec(v_val_4869_);
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5112_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_4874_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_4874_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
lean_dec(v_a_4868_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v___x_5121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8);
v___x_5122_ = l_Lean_indentExpr(v_a_4866_);
v___x_5123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5121_);
lean_ctor_set(v___x_5123_, 1, v___x_5122_);
v___x_5124_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5123_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
return v___x_5124_;
}
}
else
{
lean_dec(v_a_4866_);
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
return v___x_4867_;
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5125_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_4865_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_4865_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
lean_dec_ref_known(v___x_4860_, 2);
lean_dec(v_val_4857_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5133_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_4863_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_4863_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
else
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
lean_dec(v_a_4853_);
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v___x_5141_ = lean_box(0);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 0, v___x_5141_);
v___x_5143_ = v___x_4855_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec(v_a_4851_);
lean_dec_ref(v_type_4838_);
v_a_5146_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_4852_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_4852_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v_type_4838_);
v_a_5154_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_4850_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_4850_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_);
lean_dec(v_a_5172_);
lean_dec_ref(v_a_5171_);
lean_dec(v_a_5170_);
lean_dec_ref(v_a_5169_);
lean_dec(v_a_5168_);
lean_dec_ref(v_a_5167_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec(v_a_5163_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5175_, lean_object* v_msg_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
lean_object* v___x_5188_; 
v___x_5188_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5176_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5189_, lean_object* v_msg_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5189_, v_msg_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec(v___y_5191_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5203_, lean_object* v_a_5204_, lean_object* v_s_5205_){
_start:
{
lean_object* v_structs_5206_; lean_object* v_typeIdOf_5207_; lean_object* v_exprToStructId_5208_; lean_object* v_exprToStructIdEntries_5209_; lean_object* v_forbiddenNatModules_5210_; lean_object* v_natStructs_5211_; lean_object* v_natTypeIdOf_5212_; lean_object* v_exprToNatStructId_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5221_; 
v_structs_5206_ = lean_ctor_get(v_s_5205_, 0);
v_typeIdOf_5207_ = lean_ctor_get(v_s_5205_, 1);
v_exprToStructId_5208_ = lean_ctor_get(v_s_5205_, 2);
v_exprToStructIdEntries_5209_ = lean_ctor_get(v_s_5205_, 3);
v_forbiddenNatModules_5210_ = lean_ctor_get(v_s_5205_, 4);
v_natStructs_5211_ = lean_ctor_get(v_s_5205_, 5);
v_natTypeIdOf_5212_ = lean_ctor_get(v_s_5205_, 6);
v_exprToNatStructId_5213_ = lean_ctor_get(v_s_5205_, 7);
v_isSharedCheck_5221_ = !lean_is_exclusive(v_s_5205_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5215_ = v_s_5205_;
v_isShared_5216_ = v_isSharedCheck_5221_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_exprToNatStructId_5213_);
lean_inc(v_natTypeIdOf_5212_);
lean_inc(v_natStructs_5211_);
lean_inc(v_forbiddenNatModules_5210_);
lean_inc(v_exprToStructIdEntries_5209_);
lean_inc(v_exprToStructId_5208_);
lean_inc(v_typeIdOf_5207_);
lean_inc(v_structs_5206_);
lean_dec(v_s_5205_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5221_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5217_; lean_object* v___x_5219_; 
v___x_5217_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5212_, v_type_5203_, v_a_5204_);
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 6, v___x_5217_);
v___x_5219_ = v___x_5215_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_structs_5206_);
lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_typeIdOf_5207_);
lean_ctor_set(v_reuseFailAlloc_5220_, 2, v_exprToStructId_5208_);
lean_ctor_set(v_reuseFailAlloc_5220_, 3, v_exprToStructIdEntries_5209_);
lean_ctor_set(v_reuseFailAlloc_5220_, 4, v_forbiddenNatModules_5210_);
lean_ctor_set(v_reuseFailAlloc_5220_, 5, v_natStructs_5211_);
lean_ctor_set(v_reuseFailAlloc_5220_, 6, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5220_, 7, v_exprToNatStructId_5213_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5222_, lean_object* v_i_5223_, lean_object* v_k_5224_){
_start:
{
lean_object* v___x_5225_; uint8_t v___x_5226_; 
v___x_5225_ = lean_array_get_size(v_keys_5222_);
v___x_5226_ = lean_nat_dec_lt(v_i_5223_, v___x_5225_);
if (v___x_5226_ == 0)
{
lean_dec(v_i_5223_);
return v___x_5226_;
}
else
{
lean_object* v_k_x27_5227_; uint8_t v___x_5228_; 
v_k_x27_5227_ = lean_array_fget_borrowed(v_keys_5222_, v_i_5223_);
v___x_5228_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_5224_, v_k_x27_5227_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5229_ = lean_unsigned_to_nat(1u);
v___x_5230_ = lean_nat_add(v_i_5223_, v___x_5229_);
lean_dec(v_i_5223_);
v_i_5223_ = v___x_5230_;
goto _start;
}
else
{
lean_dec(v_i_5223_);
return v___x_5228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5232_, lean_object* v_i_5233_, lean_object* v_k_5234_){
_start:
{
uint8_t v_res_5235_; lean_object* v_r_5236_; 
v_res_5235_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5232_, v_i_5233_, v_k_5234_);
lean_dec_ref(v_k_5234_);
lean_dec_ref(v_keys_5232_);
v_r_5236_ = lean_box(v_res_5235_);
return v_r_5236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5237_, size_t v_x_5238_, lean_object* v_x_5239_){
_start:
{
if (lean_obj_tag(v_x_5237_) == 0)
{
lean_object* v_es_5240_; lean_object* v___x_5241_; size_t v___x_5242_; size_t v___x_5243_; lean_object* v_j_5244_; lean_object* v___x_5245_; 
v_es_5240_ = lean_ctor_get(v_x_5237_, 0);
v___x_5241_ = lean_box(2);
v___x_5242_ = ((size_t)31ULL);
v___x_5243_ = lean_usize_land(v_x_5238_, v___x_5242_);
v_j_5244_ = lean_usize_to_nat(v___x_5243_);
v___x_5245_ = lean_array_get_borrowed(v___x_5241_, v_es_5240_, v_j_5244_);
lean_dec(v_j_5244_);
switch(lean_obj_tag(v___x_5245_))
{
case 0:
{
lean_object* v_key_5246_; uint8_t v___x_5247_; 
v_key_5246_ = lean_ctor_get(v___x_5245_, 0);
v___x_5247_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_5239_, v_key_5246_);
return v___x_5247_;
}
case 1:
{
lean_object* v_node_5248_; size_t v___x_5249_; size_t v___x_5250_; 
v_node_5248_ = lean_ctor_get(v___x_5245_, 0);
v___x_5249_ = ((size_t)5ULL);
v___x_5250_ = lean_usize_shift_right(v_x_5238_, v___x_5249_);
v_x_5237_ = v_node_5248_;
v_x_5238_ = v___x_5250_;
goto _start;
}
default: 
{
uint8_t v___x_5252_; 
v___x_5252_ = 0;
return v___x_5252_;
}
}
}
else
{
lean_object* v_ks_5253_; lean_object* v___x_5254_; uint8_t v___x_5255_; 
v_ks_5253_ = lean_ctor_get(v_x_5237_, 0);
v___x_5254_ = lean_unsigned_to_nat(0u);
v___x_5255_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5253_, v___x_5254_, v_x_5239_);
return v___x_5255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5256_, lean_object* v_x_5257_, lean_object* v_x_5258_){
_start:
{
size_t v_x_10639__boxed_5259_; uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_x_10639__boxed_5259_ = lean_unbox_usize(v_x_5257_);
lean_dec(v_x_5257_);
v_res_5260_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5256_, v_x_10639__boxed_5259_, v_x_5258_);
lean_dec_ref(v_x_5258_);
lean_dec_ref(v_x_5256_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5262_, lean_object* v_x_5263_){
_start:
{
uint64_t v___x_5264_; size_t v___x_5265_; uint8_t v___x_5266_; 
v___x_5264_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_5263_);
v___x_5265_ = lean_uint64_to_usize(v___x_5264_);
v___x_5266_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5262_, v___x_5265_, v_x_5263_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5267_, lean_object* v_x_5268_){
_start:
{
uint8_t v_res_5269_; lean_object* v_r_5270_; 
v_res_5269_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5267_, v_x_5268_);
lean_dec_ref(v_x_5268_);
lean_dec_ref(v_x_5267_);
v_r_5270_ = lean_box(v_res_5269_);
return v_r_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v___x_5283_; 
v___x_5283_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5274_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5373_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5286_ = v___x_5283_;
v_isShared_5287_ = v_isSharedCheck_5373_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5373_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
uint8_t v_linarith_5288_; 
v_linarith_5288_ = lean_ctor_get_uint8(v_a_5284_, sizeof(void*)*13 + 22);
lean_dec(v_a_5284_);
if (v_linarith_5288_ == 0)
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
lean_dec_ref(v_type_5271_);
v___x_5289_ = lean_box(0);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5289_);
v___x_5291_ = v___x_5286_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
else
{
lean_object* v___x_5293_; 
lean_del_object(v___x_5286_);
v___x_5293_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5272_, v_a_5280_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5364_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5296_ = v___x_5293_;
v_isShared_5297_ = v_isSharedCheck_5364_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5293_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5364_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v_forbiddenNatModules_5298_; uint8_t v___x_5299_; 
v_forbiddenNatModules_5298_ = lean_ctor_get(v_a_5294_, 4);
lean_inc_ref(v_forbiddenNatModules_5298_);
lean_dec(v_a_5294_);
v___x_5299_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5298_, v_type_5271_);
lean_dec_ref(v_forbiddenNatModules_5298_);
if (v___x_5299_ == 0)
{
lean_object* v___x_5300_; 
lean_del_object(v___x_5296_);
lean_inc_ref(v_type_5271_);
v___x_5300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5351_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5303_ = v___x_5300_;
v_isShared_5304_ = v_isSharedCheck_5351_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5300_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5351_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
uint8_t v___x_5305_; 
v___x_5305_ = lean_unbox(v_a_5301_);
lean_dec(v_a_5301_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
lean_del_object(v___x_5303_);
v___x_5306_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5272_, v_a_5280_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5338_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5309_ = v___x_5306_;
v_isShared_5310_ = v_isSharedCheck_5338_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5306_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5338_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v_natTypeIdOf_5311_; lean_object* v___x_5312_; 
v_natTypeIdOf_5311_ = lean_ctor_get(v_a_5307_, 6);
lean_inc_ref(v_natTypeIdOf_5311_);
lean_dec(v_a_5307_);
v___x_5312_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5311_, v_type_5271_);
lean_dec_ref(v_natTypeIdOf_5311_);
if (lean_obj_tag(v___x_5312_) == 1)
{
lean_object* v_val_5313_; lean_object* v___x_5315_; 
lean_dec_ref(v_type_5271_);
v_val_5313_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v_val_5313_);
lean_dec_ref_known(v___x_5312_, 1);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v_val_5313_);
v___x_5315_ = v___x_5309_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_val_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
else
{
lean_object* v___x_5317_; 
lean_dec(v___x_5312_);
lean_del_object(v___x_5309_);
lean_inc_ref(v_type_5271_);
v___x_5317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; lean_object* v___f_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc_n(v_a_5318_, 2);
lean_dec_ref_known(v___x_5317_, 1);
v___f_5319_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5319_, 0, v_type_5271_);
lean_closure_set(v___f_5319_, 1, v_a_5318_);
v___x_5320_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5321_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5320_, v___f_5319_, v_a_5272_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5328_ == 0)
{
lean_object* v_unused_5329_; 
v_unused_5329_ = lean_ctor_get(v___x_5321_, 0);
lean_dec(v_unused_5329_);
v___x_5323_ = v___x_5321_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_dec(v___x_5321_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v_a_5318_);
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5318_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
lean_dec(v_a_5318_);
v_a_5330_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5321_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5321_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
else
{
lean_dec_ref(v_type_5271_);
return v___x_5317_;
}
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec_ref(v_type_5271_);
v_a_5339_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5306_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5306_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
else
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
lean_dec_ref(v_type_5271_);
v___x_5347_ = lean_box(0);
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 0, v___x_5347_);
v___x_5349_ = v___x_5303_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec_ref(v_type_5271_);
v_a_5352_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5300_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5300_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
else
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
lean_dec_ref(v_type_5271_);
v___x_5360_ = lean_box(0);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 0, v___x_5360_);
v___x_5362_ = v___x_5296_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v_type_5271_);
v_a_5365_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5293_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5293_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec_ref(v_type_5271_);
v_a_5374_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5283_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5283_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec_ref(v_a_5389_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_a_5384_);
lean_dec(v_a_5383_);
return v_res_5394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5395_, lean_object* v_x_5396_, lean_object* v_x_5397_){
_start:
{
uint8_t v___x_5398_; 
v___x_5398_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5396_, v_x_5397_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5399_, lean_object* v_x_5400_, lean_object* v_x_5401_){
_start:
{
uint8_t v_res_5402_; lean_object* v_r_5403_; 
v_res_5402_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5399_, v_x_5400_, v_x_5401_);
lean_dec_ref(v_x_5401_);
lean_dec_ref(v_x_5400_);
v_r_5403_ = lean_box(v_res_5402_);
return v_r_5403_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5404_, lean_object* v_x_5405_, size_t v_x_5406_, lean_object* v_x_5407_){
_start:
{
uint8_t v___x_5408_; 
v___x_5408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5405_, v_x_5406_, v_x_5407_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5409_, lean_object* v_x_5410_, lean_object* v_x_5411_, lean_object* v_x_5412_){
_start:
{
size_t v_x_10897__boxed_5413_; uint8_t v_res_5414_; lean_object* v_r_5415_; 
v_x_10897__boxed_5413_ = lean_unbox_usize(v_x_5411_);
lean_dec(v_x_5411_);
v_res_5414_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5409_, v_x_5410_, v_x_10897__boxed_5413_, v_x_5412_);
lean_dec_ref(v_x_5412_);
lean_dec_ref(v_x_5410_);
v_r_5415_ = lean_box(v_res_5414_);
return v_r_5415_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5416_, lean_object* v_keys_5417_, lean_object* v_vals_5418_, lean_object* v_heq_5419_, lean_object* v_i_5420_, lean_object* v_k_5421_){
_start:
{
uint8_t v___x_5422_; 
v___x_5422_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5417_, v_i_5420_, v_k_5421_);
return v___x_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5423_, lean_object* v_keys_5424_, lean_object* v_vals_5425_, lean_object* v_heq_5426_, lean_object* v_i_5427_, lean_object* v_k_5428_){
_start:
{
uint8_t v_res_5429_; lean_object* v_r_5430_; 
v_res_5429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5423_, v_keys_5424_, v_vals_5425_, v_heq_5426_, v_i_5427_, v_k_5428_);
lean_dec_ref(v_k_5428_);
lean_dec_ref(v_vals_5425_);
lean_dec_ref(v_keys_5424_);
v_r_5430_ = lean_box(v_res_5429_);
return v_r_5430_;
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
