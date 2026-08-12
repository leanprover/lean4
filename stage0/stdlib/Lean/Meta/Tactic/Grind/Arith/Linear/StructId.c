// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.OrderInsts import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Tactic.Grind.Arith.Insts import Init.Grind.Module.Envelope import Lean.OrderLevel
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkRawNatLit(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(75, 224, 25, 76, 51, 82, 222, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toAddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(205, 72, 3, 192, 99, 106, 67, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "AddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toAddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(143, 195, 31, 215, 150, 195, 138, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(93, 134, 71, 250, 19, 181, 172, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64_value;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ofNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 244, 42, 211, 144, 181, 88, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(28, 233, 202, 97, 203, 184, 134, 106)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(124, 125, 226, 15, 218, 207, 24, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toOfNat0"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 59, 186, 84, 178, 224, 2, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(28, 233, 202, 97, 203, 184, 134, 106)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(85, 115, 161, 225, 76, 32, 159, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(220, 51, 153, 189, 12, 154, 25, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34_value),LEAN_SCALAR_PTR_LITERAL(144, 111, 86, 72, 218, 93, 29, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(245, 167, 193, 225, 213, 13, 125, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(168, 238, 174, 79, 173, 177, 80, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(89, 64, 142, 19, 104, 31, 117, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instIsLinearOrderQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(230, 87, 230, 220, 201, 183, 231, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instLawfulOrderLT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(161, 160, 205, 130, 233, 12, 158, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(64, 237, 13, 63, 87, 160, 117, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instLEQOfOrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(161, 134, 150, 210, 182, 168, 122, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instLTQOfOrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(159, 207, 2, 71, 208, 154, 4, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instIsPreorderQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(189, 25, 119, 3, 206, 38, 180, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instOrderedAddQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30_value),LEAN_SCALAR_PTR_LITERAL(120, 114, 202, 218, 72, 0, 10, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4;
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
v_lia_802_ = lean_ctor_get_uint8(v_a_801_, sizeof(void*)*14 + 23);
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
lean_object* v_val_1762_; lean_object* v_val_1763_; lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1762_ = lean_ctor_get(v_leInst_x3f_1746_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v_leInst_x3f_1746_, 1);
v_val_1763_ = lean_ctor_get(v_parentInst_x3f_1747_, 0);
lean_inc(v_val_1763_);
lean_dec_ref_known(v_parentInst_x3f_1747_, 1);
v_val_1764_ = lean_ctor_get(v_childInst_x3f_1748_, 0);
v___x_1765_ = l_Lean_leCarrierIsSort(v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_____do__lift_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; uint8_t v___x_1819_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1819_ = lean_unbox(v_a_1766_);
lean_dec(v_a_1766_);
if (v___x_1819_ == 0)
{
v_____do__lift_1768_ = v_u_1750_;
v___y_1769_ = v_a_1752_;
v___y_1770_ = v_a_1753_;
v___y_1771_ = v_a_1754_;
v___y_1772_ = v_a_1755_;
v___y_1773_ = v_a_1756_;
v___y_1774_ = v_a_1757_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Level_succ___override(v_u_1750_);
v_____do__lift_1768_ = v___x_1820_;
v___y_1769_ = v_a_1752_;
v___y_1770_ = v_a_1753_;
v___y_1771_ = v_a_1754_;
v___y_1772_ = v_a_1755_;
v___y_1773_ = v_a_1756_;
v___y_1774_ = v_a_1757_;
goto v___jp_1767_;
}
v___jp_1767_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_____do__lift_1768_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_mkConst(v_toFieldName_1749_, v___x_1776_);
lean_inc(v_val_1764_);
v___x_1778_ = l_Lean_mkApp3(v___x_1777_, v_type_1751_, v_val_1762_, v_val_1764_);
lean_inc_ref(v___x_1778_);
lean_inc(v_val_1763_);
v___x_1779_ = l_Lean_Meta_isDefEqD(v_val_1763_, v___x_1778_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1810_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1810_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1810_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v_a_1786_; lean_object* v___x_1787_; 
lean_del_object(v___x_1782_);
lean_dec_ref_known(v_childInst_x3f_1748_, 1);
v___x_1785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1763_, v___x_1778_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1769_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v_verbose_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v_verbose_1789_ = lean_ctor_get_uint8(v_a_1788_, 0);
lean_dec(v_a_1788_);
if (v_verbose_1789_ == 0)
{
lean_dec(v_a_1786_);
goto v___jp_1759_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Sym_reportIssue(v_a_1786_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref_known(v___x_1790_, 1);
goto v___jp_1759_;
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1786_);
v_a_1799_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1787_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1787_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1763_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v_childInst_x3f_1748_);
v___x_1808_ = v___x_1782_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_childInst_x3f_1748_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1763_);
lean_dec_ref_known(v_childInst_x3f_1748_, 1);
v_a_1811_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1779_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1779_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_val_1763_);
lean_dec_ref_known(v_childInst_x3f_1748_, 1);
lean_dec(v_val_1762_);
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
v_a_1821_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1765_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1765_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref_known(v_leInst_x3f_1746_, 1);
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_parentInst_x3f_1747_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v_parentInst_x3f_1747_, 0);
lean_dec(v_unused_1837_);
v___x_1830_ = v_parentInst_x3f_1747_;
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
else
{
lean_dec(v_parentInst_x3f_1747_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1836_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_box(0);
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1832_);
v___x_1834_ = v___x_1830_;
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
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
lean_dec(v_parentInst_x3f_1747_);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_leInst_x3f_1746_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v_leInst_x3f_1746_, 0);
lean_dec(v_unused_1846_);
v___x_1839_ = v_leInst_x3f_1746_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v_leInst_x3f_1746_);
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
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v_type_1751_);
lean_dec(v_u_1750_);
lean_dec(v_toFieldName_1749_);
lean_dec(v_childInst_x3f_1748_);
lean_dec(v_parentInst_x3f_1747_);
lean_dec(v_leInst_x3f_1746_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1849_, lean_object* v_parentInst_x3f_1850_, lean_object* v_childInst_x3f_1851_, lean_object* v_toFieldName_1852_, lean_object* v_u_1853_, lean_object* v_type_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1849_, v_parentInst_x3f_1850_, v_childInst_x3f_1851_, v_toFieldName_1852_, v_u_1853_, v_type_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1863_, lean_object* v_parentInst_x3f_1864_, lean_object* v_childInst_x3f_1865_, lean_object* v_toFieldName_1866_, lean_object* v_u_1867_, lean_object* v_type_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1863_, v_parentInst_x3f_1864_, v_childInst_x3f_1865_, v_toFieldName_1866_, v_u_1867_, v_type_1868_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1881_ = _args[0];
lean_object* v_parentInst_x3f_1882_ = _args[1];
lean_object* v_childInst_x3f_1883_ = _args[2];
lean_object* v_toFieldName_1884_ = _args[3];
lean_object* v_u_1885_ = _args[4];
lean_object* v_type_1886_ = _args[5];
lean_object* v_a_1887_ = _args[6];
lean_object* v_a_1888_ = _args[7];
lean_object* v_a_1889_ = _args[8];
lean_object* v_a_1890_ = _args[9];
lean_object* v_a_1891_ = _args[10];
lean_object* v_a_1892_ = _args[11];
lean_object* v_a_1893_ = _args[12];
lean_object* v_a_1894_ = _args[13];
lean_object* v_a_1895_ = _args[14];
lean_object* v_a_1896_ = _args[15];
lean_object* v_a_1897_ = _args[16];
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1881_, v_parentInst_x3f_1882_, v_childInst_x3f_1883_, v_toFieldName_1884_, v_u_1885_, v_type_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec(v_a_1887_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1899_, lean_object* v_inst_1900_, lean_object* v_toFieldName_1901_, lean_object* v_u_1902_, lean_object* v_type_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_toField_1912_; lean_object* v___x_1913_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_u_1902_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lean_mkConst(v_toFieldName_1901_, v___x_1910_);
v_toField_1912_ = l_Lean_mkAppB(v___x_1911_, v_type_1903_, v_inst_1900_);
v___x_1913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1899_, v_toField_1912_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1914_, lean_object* v_inst_1915_, lean_object* v_toFieldName_1916_, lean_object* v_u_1917_, lean_object* v_type_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1914_, v_inst_1915_, v_toFieldName_1916_, v_u_1917_, v_type_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1925_, lean_object* v_inst_1926_, lean_object* v_toFieldName_1927_, lean_object* v_u_1928_, lean_object* v_type_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1925_, v_inst_1926_, v_toFieldName_1927_, v_u_1928_, v_type_1929_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1942_, lean_object* v_inst_1943_, lean_object* v_toFieldName_1944_, lean_object* v_u_1945_, lean_object* v_type_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1942_, v_inst_1943_, v_toFieldName_1944_, v_u_1945_, v_type_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
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
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1959_, lean_object* v_inst_1960_, lean_object* v_toFieldName_1961_, lean_object* v_toHeteroName_1962_, lean_object* v_u_1963_, lean_object* v_type_1964_, lean_object* v_extraType_x3f_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_toField_1974_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_u_1963_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
lean_inc_ref(v___x_1972_);
v___x_1973_ = l_Lean_mkConst(v_toFieldName_1961_, v___x_1972_);
lean_inc_ref(v_type_1964_);
v_toField_1974_ = l_Lean_mkAppB(v___x_1973_, v_type_1964_, v_inst_1960_);
if (lean_obj_tag(v_extraType_x3f_1965_) == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = l_Lean_mkConst(v_toHeteroName_1962_, v___x_1972_);
v___x_1976_ = l_Lean_mkAppB(v___x_1975_, v_type_1964_, v_toField_1974_);
v___x_1977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1959_, v___x_1976_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_1977_;
}
else
{
lean_object* v_val_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_val_1978_ = lean_ctor_get(v_extraType_x3f_1965_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v_extraType_x3f_1965_, 1);
v___x_1979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v___x_1972_);
v___x_1981_ = l_Lean_mkConst(v_toHeteroName_1962_, v___x_1980_);
v___x_1982_ = l_Lean_mkApp3(v___x_1981_, v_val_1978_, v_type_1964_, v_toField_1974_);
v___x_1983_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1959_, v___x_1982_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1984_, lean_object* v_inst_1985_, lean_object* v_toFieldName_1986_, lean_object* v_toHeteroName_1987_, lean_object* v_u_1988_, lean_object* v_type_1989_, lean_object* v_extraType_x3f_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1984_, v_inst_1985_, v_toFieldName_1986_, v_toHeteroName_1987_, v_u_1988_, v_type_1989_, v_extraType_x3f_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1997_, lean_object* v_inst_1998_, lean_object* v_toFieldName_1999_, lean_object* v_toHeteroName_2000_, lean_object* v_u_2001_, lean_object* v_type_2002_, lean_object* v_extraType_x3f_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1997_, v_inst_1998_, v_toFieldName_1999_, v_toHeteroName_2000_, v_u_2001_, v_type_2002_, v_extraType_x3f_2003_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_2016_ = _args[0];
lean_object* v_inst_2017_ = _args[1];
lean_object* v_toFieldName_2018_ = _args[2];
lean_object* v_toHeteroName_2019_ = _args[3];
lean_object* v_u_2020_ = _args[4];
lean_object* v_type_2021_ = _args[5];
lean_object* v_extraType_x3f_2022_ = _args[6];
lean_object* v_a_2023_ = _args[7];
lean_object* v_a_2024_ = _args[8];
lean_object* v_a_2025_ = _args[9];
lean_object* v_a_2026_ = _args[10];
lean_object* v_a_2027_ = _args[11];
lean_object* v_a_2028_ = _args[12];
lean_object* v_a_2029_ = _args[13];
lean_object* v_a_2030_ = _args[14];
lean_object* v_a_2031_ = _args[15];
lean_object* v_a_2032_ = _args[16];
lean_object* v_a_2033_ = _args[17];
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2016_, v_inst_2017_, v_toFieldName_2018_, v_toHeteroName_2019_, v_u_2020_, v_type_2021_, v_extraType_x3f_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec(v_a_2023_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2039_, lean_object* v_type_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v_smulType_2056_; lean_object* v___x_2057_; 
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2050_ = lean_box(0);
lean_inc(v_u_2039_);
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_u_2039_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_u_2039_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2049_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_inc_ref(v___x_2053_);
v___x_2054_ = l_Lean_mkConst(v___x_2048_, v___x_2053_);
v___x_2055_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2040_, 2);
v_smulType_2056_ = l_Lean_mkApp3(v___x_2054_, v___x_2055_, v_type_2040_, v_type_2040_);
v___x_2057_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2056_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2094_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
if (lean_obj_tag(v_a_2058_) == 1)
{
lean_object* v_val_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2089_; 
lean_del_object(v___x_2060_);
v_val_2062_ = lean_ctor_get(v_a_2058_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_a_2058_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2064_ = v_a_2058_;
v_isShared_2065_ = v_isSharedCheck_2089_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_val_2062_);
lean_dec(v_a_2058_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2089_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2067_ = l_Lean_mkConst(v___x_2066_, v___x_2053_);
lean_inc_ref(v_type_2040_);
v___x_2068_ = l_Lean_mkApp4(v___x_2067_, v___x_2055_, v_type_2040_, v_type_2040_, v_val_2062_);
v___x_2069_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2068_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2080_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2080_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_a_2070_);
v___x_2075_ = v___x_2064_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_del_object(v___x_2064_);
v_a_2081_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2069_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2069_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
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
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_a_2058_);
lean_dec_ref_known(v___x_2053_, 2);
lean_dec_ref(v_type_2040_);
v___x_2090_ = lean_box(0);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2090_);
v___x_2092_ = v___x_2060_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2053_, 2);
lean_dec_ref(v_type_2040_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2095_, lean_object* v_type_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2095_, v_type_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2105_, lean_object* v_type_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2105_, v_type_2106_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2119_, lean_object* v_type_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2119_, v_type_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec(v_a_2121_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2133_, lean_object* v_type_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_smulType_2150_; lean_object* v___x_2151_; 
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2144_ = lean_box(0);
lean_inc(v_u_2133_);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_u_2133_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_u_2133_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2143_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
lean_inc_ref(v___x_2147_);
v___x_2148_ = l_Lean_mkConst(v___x_2142_, v___x_2147_);
v___x_2149_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2134_, 2);
v_smulType_2150_ = l_Lean_mkApp3(v___x_2148_, v___x_2149_, v_type_2134_, v_type_2134_);
v___x_2151_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2150_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2188_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2188_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2188_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
if (lean_obj_tag(v_a_2152_) == 1)
{
lean_object* v_val_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2183_; 
lean_del_object(v___x_2154_);
v_val_2156_ = lean_ctor_get(v_a_2152_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2158_ = v_a_2152_;
v_isShared_2159_ = v_isSharedCheck_2183_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_val_2156_);
lean_dec(v_a_2152_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2183_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2161_ = l_Lean_mkConst(v___x_2160_, v___x_2147_);
lean_inc_ref(v_type_2134_);
v___x_2162_ = l_Lean_mkApp4(v___x_2161_, v___x_2149_, v_type_2134_, v_type_2134_, v_val_2156_);
v___x_2163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2162_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2174_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2174_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v_a_2164_);
v___x_2169_ = v___x_2158_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2158_);
v_a_2175_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2163_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2163_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
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
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec(v_a_2152_);
lean_dec_ref_known(v___x_2147_, 2);
lean_dec_ref(v_type_2134_);
v___x_2184_ = lean_box(0);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2184_);
v___x_2186_ = v___x_2154_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2147_, 2);
lean_dec_ref(v_type_2134_);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2189_, lean_object* v_type_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2189_, v_type_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2199_, lean_object* v_type_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2199_, v_type_2200_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2213_, lean_object* v_type_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2213_, v_type_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec(v_a_2215_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v_ks_2231_; lean_object* v_vs_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2258_; 
v_ks_2231_ = lean_ctor_get(v_x_2227_, 0);
v_vs_2232_ = lean_ctor_get(v_x_2227_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_x_2227_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2234_ = v_x_2227_;
v_isShared_2235_ = v_isSharedCheck_2258_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_vs_2232_);
lean_inc(v_ks_2231_);
lean_dec(v_x_2227_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2258_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = lean_array_get_size(v_ks_2231_);
v___x_2237_ = lean_nat_dec_lt(v_x_2228_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_x_2228_);
v___x_2238_ = lean_array_push(v_ks_2231_, v_x_2229_);
v___x_2239_ = lean_array_push(v_vs_2232_, v_x_2230_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2239_);
lean_ctor_set(v___x_2234_, 0, v___x_2238_);
v___x_2241_ = v___x_2234_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
lean_object* v_k_x27_2243_; size_t v___x_2244_; size_t v___x_2245_; uint8_t v___x_2246_; 
v_k_x27_2243_ = lean_array_fget_borrowed(v_ks_2231_, v_x_2228_);
v___x_2244_ = lean_ptr_addr(v_x_2229_);
v___x_2245_ = lean_ptr_addr(v_k_x27_2243_);
v___x_2246_ = lean_usize_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2248_; 
if (v_isShared_2235_ == 0)
{
v___x_2248_ = v___x_2234_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_ks_2231_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_vs_2232_);
v___x_2248_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v_x_2228_, v___x_2249_);
lean_dec(v_x_2228_);
v_x_2227_ = v___x_2248_;
v_x_2228_ = v___x_2250_;
goto _start;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = lean_array_fset(v_ks_2231_, v_x_2228_, v_x_2229_);
v___x_2254_ = lean_array_fset(v_vs_2232_, v_x_2228_, v_x_2230_);
lean_dec(v_x_2228_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 1, v___x_2254_);
lean_ctor_set(v___x_2234_, 0, v___x_2253_);
v___x_2256_ = v___x_2234_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2254_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2259_, lean_object* v_k_2260_, lean_object* v_v_2261_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2259_, v___x_2262_, v_k_2260_, v_v_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2265_, size_t v_x_2266_, size_t v_x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v_es_2270_; size_t v___x_2271_; size_t v___x_2272_; lean_object* v_j_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_es_2270_ = lean_ctor_get(v_x_2265_, 0);
v___x_2271_ = ((size_t)31ULL);
v___x_2272_ = lean_usize_land(v_x_2266_, v___x_2271_);
v_j_2273_ = lean_usize_to_nat(v___x_2272_);
v___x_2274_ = lean_array_get_size(v_es_2270_);
v___x_2275_ = lean_nat_dec_lt(v_j_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec(v_j_2273_);
lean_dec(v_x_2269_);
lean_dec_ref(v_x_2268_);
return v_x_2265_;
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2316_; 
lean_inc_ref(v_es_2270_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2317_);
v___x_2277_ = v_x_2265_;
v_isShared_2278_ = v_isSharedCheck_2316_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2265_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2316_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_v_2279_; lean_object* v___x_2280_; lean_object* v_xs_x27_2281_; lean_object* v___y_2283_; 
v_v_2279_ = lean_array_fget(v_es_2270_, v_j_2273_);
v___x_2280_ = lean_box(0);
v_xs_x27_2281_ = lean_array_fset(v_es_2270_, v_j_2273_, v___x_2280_);
switch(lean_obj_tag(v_v_2279_))
{
case 0:
{
lean_object* v_key_2288_; lean_object* v_val_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2301_; 
v_key_2288_ = lean_ctor_get(v_v_2279_, 0);
v_val_2289_ = lean_ctor_get(v_v_2279_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_v_2279_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2291_ = v_v_2279_;
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_val_2289_);
lean_inc(v_key_2288_);
lean_dec(v_v_2279_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2301_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
size_t v___x_2293_; size_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_ptr_addr(v_x_2268_);
v___x_2294_ = lean_ptr_addr(v_key_2288_);
v___x_2295_ = lean_usize_dec_eq(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_del_object(v___x_2291_);
v___x_2296_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2288_, v_val_2289_, v_x_2268_, v_x_2269_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___y_2283_ = v___x_2297_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2299_; 
lean_dec(v_val_2289_);
lean_dec(v_key_2288_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v_x_2269_);
lean_ctor_set(v___x_2291_, 0, v_x_2268_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_x_2268_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_x_2269_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
v___y_2283_ = v___x_2299_;
goto v___jp_2282_;
}
}
}
}
case 1:
{
lean_object* v_node_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2314_; 
v_node_2302_ = lean_ctor_get(v_v_2279_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_v_2279_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2304_ = v_v_2279_;
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_node_2302_);
lean_dec(v_v_2279_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2306_ = ((size_t)5ULL);
v___x_2307_ = lean_usize_shift_right(v_x_2266_, v___x_2306_);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_add(v_x_2267_, v___x_2308_);
v___x_2310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2302_, v___x_2307_, v___x_2309_, v_x_2268_, v_x_2269_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2310_);
v___x_2312_ = v___x_2304_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
v___y_2283_ = v___x_2312_;
goto v___jp_2282_;
}
}
}
default: 
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_x_2268_);
lean_ctor_set(v___x_2315_, 1, v_x_2269_);
v___y_2283_ = v___x_2315_;
goto v___jp_2282_;
}
}
v___jp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_array_fset(v_xs_x27_2281_, v_j_2273_, v___y_2283_);
lean_dec(v_j_2273_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2284_);
v___x_2286_ = v___x_2277_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_ks_2318_; lean_object* v_vs_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2339_; 
v_ks_2318_ = lean_ctor_get(v_x_2265_, 0);
v_vs_2319_ = lean_ctor_get(v_x_2265_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2321_ = v_x_2265_;
v_isShared_2322_ = v_isSharedCheck_2339_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_vs_2319_);
lean_inc(v_ks_2318_);
lean_dec(v_x_2265_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2339_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_ks_2318_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_vs_2319_);
v___x_2324_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v_newNode_2325_; uint8_t v___y_2327_; size_t v___x_2333_; uint8_t v___x_2334_; 
v_newNode_2325_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2324_, v_x_2268_, v_x_2269_);
v___x_2333_ = ((size_t)7ULL);
v___x_2334_ = lean_usize_dec_le(v___x_2333_, v_x_2267_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2335_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2325_);
v___x_2336_ = lean_unsigned_to_nat(4u);
v___x_2337_ = lean_nat_dec_lt(v___x_2335_, v___x_2336_);
lean_dec(v___x_2335_);
v___y_2327_ = v___x_2337_;
goto v___jp_2326_;
}
else
{
v___y_2327_ = v___x_2334_;
goto v___jp_2326_;
}
v___jp_2326_:
{
if (v___y_2327_ == 0)
{
lean_object* v_ks_2328_; lean_object* v_vs_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_ks_2328_ = lean_ctor_get(v_newNode_2325_, 0);
lean_inc_ref(v_ks_2328_);
v_vs_2329_ = lean_ctor_get(v_newNode_2325_, 1);
lean_inc_ref(v_vs_2329_);
lean_dec_ref(v_newNode_2325_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2332_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2267_, v_ks_2328_, v_vs_2329_, v___x_2330_, v___x_2331_);
lean_dec_ref(v_vs_2329_);
lean_dec_ref(v_ks_2328_);
return v___x_2332_;
}
else
{
return v_newNode_2325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2340_, lean_object* v_keys_2341_, lean_object* v_vals_2342_, lean_object* v_i_2343_, lean_object* v_entries_2344_){
_start:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = lean_array_get_size(v_keys_2341_);
v___x_2346_ = lean_nat_dec_lt(v_i_2343_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_dec(v_i_2343_);
return v_entries_2344_;
}
else
{
lean_object* v_k_2347_; lean_object* v_v_2348_; size_t v___x_2349_; size_t v___x_2350_; size_t v___x_2351_; uint64_t v___x_2352_; size_t v_h_2353_; size_t v___x_2354_; lean_object* v___x_2355_; size_t v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; size_t v_h_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_k_2347_ = lean_array_fget_borrowed(v_keys_2341_, v_i_2343_);
v_v_2348_ = lean_array_fget_borrowed(v_vals_2342_, v_i_2343_);
v___x_2349_ = lean_ptr_addr(v_k_2347_);
v___x_2350_ = ((size_t)3ULL);
v___x_2351_ = lean_usize_shift_right(v___x_2349_, v___x_2350_);
v___x_2352_ = lean_usize_to_uint64(v___x_2351_);
v_h_2353_ = lean_uint64_to_usize(v___x_2352_);
v___x_2354_ = ((size_t)5ULL);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = lean_usize_sub(v_depth_2340_, v___x_2356_);
v___x_2358_ = lean_usize_mul(v___x_2354_, v___x_2357_);
v_h_2359_ = lean_usize_shift_right(v_h_2353_, v___x_2358_);
v___x_2360_ = lean_nat_add(v_i_2343_, v___x_2355_);
lean_dec(v_i_2343_);
lean_inc(v_v_2348_);
lean_inc(v_k_2347_);
v___x_2361_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2344_, v_h_2359_, v_depth_2340_, v_k_2347_, v_v_2348_);
v_i_2343_ = v___x_2360_;
v_entries_2344_ = v___x_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2363_, lean_object* v_keys_2364_, lean_object* v_vals_2365_, lean_object* v_i_2366_, lean_object* v_entries_2367_){
_start:
{
size_t v_depth_boxed_2368_; lean_object* v_res_2369_; 
v_depth_boxed_2368_ = lean_unbox_usize(v_depth_2363_);
lean_dec(v_depth_2363_);
v_res_2369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2368_, v_keys_2364_, v_vals_2365_, v_i_2366_, v_entries_2367_);
lean_dec_ref(v_vals_2365_);
lean_dec_ref(v_keys_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
size_t v_x_801343__boxed_2375_; size_t v_x_801344__boxed_2376_; lean_object* v_res_2377_; 
v_x_801343__boxed_2375_ = lean_unbox_usize(v_x_2371_);
lean_dec(v_x_2371_);
v_x_801344__boxed_2376_ = lean_unbox_usize(v_x_2372_);
lean_dec(v_x_2372_);
v_res_2377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2370_, v_x_801343__boxed_2375_, v_x_801344__boxed_2376_, v_x_2373_, v_x_2374_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
size_t v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; uint64_t v___x_2384_; size_t v___x_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v___x_2381_ = lean_ptr_addr(v_x_2379_);
v___x_2382_ = ((size_t)3ULL);
v___x_2383_ = lean_usize_shift_right(v___x_2381_, v___x_2382_);
v___x_2384_ = lean_usize_to_uint64(v___x_2383_);
v___x_2385_ = lean_uint64_to_usize(v___x_2384_);
v___x_2386_ = ((size_t)1ULL);
v___x_2387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2378_, v___x_2385_, v___x_2386_, v_x_2379_, v_x_2380_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2388_, lean_object* v_s_2389_){
_start:
{
lean_object* v_structs_2390_; lean_object* v_typeIdOf_2391_; lean_object* v_exprToStructId_2392_; lean_object* v_exprToStructIdEntries_2393_; lean_object* v_forbiddenNatModules_2394_; lean_object* v_natStructs_2395_; lean_object* v_natTypeIdOf_2396_; lean_object* v_exprToNatStructId_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2406_; 
v_structs_2390_ = lean_ctor_get(v_s_2389_, 0);
v_typeIdOf_2391_ = lean_ctor_get(v_s_2389_, 1);
v_exprToStructId_2392_ = lean_ctor_get(v_s_2389_, 2);
v_exprToStructIdEntries_2393_ = lean_ctor_get(v_s_2389_, 3);
v_forbiddenNatModules_2394_ = lean_ctor_get(v_s_2389_, 4);
v_natStructs_2395_ = lean_ctor_get(v_s_2389_, 5);
v_natTypeIdOf_2396_ = lean_ctor_get(v_s_2389_, 6);
v_exprToNatStructId_2397_ = lean_ctor_get(v_s_2389_, 7);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_s_2389_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2399_ = v_s_2389_;
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_exprToNatStructId_2397_);
lean_inc(v_natTypeIdOf_2396_);
lean_inc(v_natStructs_2395_);
lean_inc(v_forbiddenNatModules_2394_);
lean_inc(v_exprToStructIdEntries_2393_);
lean_inc(v_exprToStructId_2392_);
lean_inc(v_typeIdOf_2391_);
lean_inc(v_structs_2390_);
lean_dec(v_s_2389_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2394_, v_type_2388_, v___x_2401_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 4, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_structs_2390_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_typeIdOf_2391_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_exprToStructId_2392_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_exprToStructIdEntries_2393_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_natStructs_2395_);
lean_ctor_set(v_reuseFailAlloc_2405_, 6, v_natTypeIdOf_2396_);
lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_exprToNatStructId_2397_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v___x_2407_, lean_object* v_s_2408_){
_start:
{
lean_object* v_structs_2409_; lean_object* v_typeIdOf_2410_; lean_object* v_exprToStructId_2411_; lean_object* v_exprToStructIdEntries_2412_; lean_object* v_forbiddenNatModules_2413_; lean_object* v_natStructs_2414_; lean_object* v_natTypeIdOf_2415_; lean_object* v_exprToNatStructId_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_structs_2409_ = lean_ctor_get(v_s_2408_, 0);
v_typeIdOf_2410_ = lean_ctor_get(v_s_2408_, 1);
v_exprToStructId_2411_ = lean_ctor_get(v_s_2408_, 2);
v_exprToStructIdEntries_2412_ = lean_ctor_get(v_s_2408_, 3);
v_forbiddenNatModules_2413_ = lean_ctor_get(v_s_2408_, 4);
v_natStructs_2414_ = lean_ctor_get(v_s_2408_, 5);
v_natTypeIdOf_2415_ = lean_ctor_get(v_s_2408_, 6);
v_exprToNatStructId_2416_ = lean_ctor_get(v_s_2408_, 7);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_s_2408_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v_s_2408_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_exprToNatStructId_2416_);
lean_inc(v_natTypeIdOf_2415_);
lean_inc(v_natStructs_2414_);
lean_inc(v_forbiddenNatModules_2413_);
lean_inc(v_exprToStructIdEntries_2412_);
lean_inc(v_exprToStructId_2411_);
lean_inc(v_typeIdOf_2410_);
lean_inc(v_structs_2409_);
lean_dec(v_s_2408_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_array_push(v_structs_2409_, v___x_2407_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_typeIdOf_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_exprToStructId_2411_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_exprToStructIdEntries_2412_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_forbiddenNatModules_2413_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_natStructs_2414_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_natTypeIdOf_2415_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_exprToNatStructId_2416_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v_a_2425_, lean_object* v_00___2426_){
_start:
{
if (lean_obj_tag(v_a_2425_) == 0)
{
uint8_t v___x_2427_; 
v___x_2427_ = 0;
return v___x_2427_;
}
else
{
uint8_t v___x_2428_; 
v___x_2428_ = 1;
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object* v_a_2429_, lean_object* v_00___2430_){
_start:
{
uint8_t v_res_2431_; lean_object* v_r_2432_; 
v_res_2431_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2429_, v_00___2430_);
lean_dec(v_a_2429_);
v_r_2432_ = lean_box(v_res_2431_);
return v_r_2432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = lean_unsigned_to_nat(32u);
v___x_2434_ = lean_mk_empty_array_with_capacity(v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1(void){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = l_Lean_mkRawNatLit(v___x_2458_);
return v___x_2459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Lean_Int_mkType;
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = l_Lean_Nat_mkType;
v___x_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___y_2560_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; uint8_t v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___x_2625_; 
lean_inc_ref(v_type_2547_);
v___x_2625_ = l_Lean_Meta_getDecLevel_x3f(v_type_2547_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_3883_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_3883_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_3883_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
if (lean_obj_tag(v_a_2626_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_3878_; 
lean_del_object(v___x_2628_);
v_val_2630_ = lean_ctor_get(v_a_2626_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_2626_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_2632_ = v_a_2626_;
v_isShared_2633_ = v_isSharedCheck_3878_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_val_2630_);
lean_dec(v_a_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_3878_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; 
lean_inc_ref(v_type_2547_);
v___x_2634_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_3877_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_3877_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_3877_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v_homomulFn_x3f_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; uint8_t v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_ltFn_x3f_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v_____do__lift_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v_leFn_x3f_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v_____do__lift_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v_charInst_x3f_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; uint8_t v___y_3299_; lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_leCarrierIsSort(v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___f_3388_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v_____do__lift_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v_____do__lift_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v_____do__lift_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_____do__lift_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v_____do__lift_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v_____do__lift_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; uint8_t v___x_3867_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
lean_inc_ref(v_type_2547_);
v___f_3388_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3388_, 0, v_type_2547_);
v___x_3867_ = lean_unbox(v_a_3387_);
lean_dec(v_a_3387_);
if (v___x_3867_ == 0)
{
lean_inc(v_val_2630_);
v_____do__lift_3832_ = v_val_2630_;
v___y_3833_ = v_a_2548_;
v___y_3834_ = v_a_2549_;
v___y_3835_ = v_a_2550_;
v___y_3836_ = v_a_2551_;
v___y_3837_ = v_a_2552_;
v___y_3838_ = v_a_2553_;
v___y_3839_ = v_a_2554_;
v___y_3840_ = v_a_2555_;
v___y_3841_ = v_a_2556_;
v___y_3842_ = v_a_2557_;
goto v___jp_3831_;
}
else
{
lean_object* v___x_3868_; 
lean_inc(v_val_2630_);
v___x_3868_ = l_Lean_Level_succ___override(v_val_2630_);
v_____do__lift_3832_ = v___x_3868_;
v___y_3833_ = v_a_2548_;
v___y_3834_ = v_a_2549_;
v___y_3835_ = v_a_2550_;
v___y_3836_ = v_a_2551_;
v___y_3837_ = v_a_2552_;
v___y_3838_ = v_a_2553_;
v___y_3839_ = v_a_2554_;
v___y_3840_ = v_a_2555_;
v___y_3841_ = v_a_2556_;
v___y_3842_ = v_a_2557_;
goto v___jp_3831_;
}
v___jp_3389_:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3405_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; uint8_t v_ring_3421_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v_ring_3421_ = lean_ctor_get_uint8(v_a_3420_, sizeof(void*)*14 + 21);
lean_dec(v_a_3420_);
if (v_ring_3421_ == 0)
{
lean_dec_ref(v___f_3388_);
v___y_3271_ = v___y_3390_;
v___y_3272_ = v___y_3392_;
v___y_3273_ = v___y_3391_;
v___y_3274_ = v___y_3393_;
v___y_3275_ = v___y_3395_;
v___y_3276_ = v___y_3396_;
v___y_3277_ = v___y_3397_;
v___y_3278_ = v___y_3398_;
v___y_3279_ = v___y_3399_;
v___y_3280_ = v___y_3400_;
v___y_3281_ = v___y_3401_;
v___y_3282_ = v___y_3402_;
v___y_3283_ = v___y_3403_;
v___y_3284_ = v___y_3418_;
v___y_3285_ = v___y_3404_;
v___y_3286_ = v___y_3405_;
v___y_3287_ = v___y_3406_;
v___y_3288_ = v___y_3407_;
v___y_3289_ = v___y_3408_;
v___y_3290_ = v___y_3409_;
v___y_3291_ = v___y_3410_;
v___y_3292_ = v___y_3411_;
v___y_3293_ = v___y_3412_;
v___y_3294_ = v___y_3413_;
v___y_3295_ = v___y_3414_;
v___y_3296_ = v___y_3415_;
v___y_3297_ = v___y_3417_;
v___y_3298_ = v___y_3416_;
v___y_3299_ = v_ring_3421_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2635_, v___x_3422_);
if (v___x_3423_ == 0)
{
lean_dec_ref(v___f_3388_);
v___y_3271_ = v___y_3390_;
v___y_3272_ = v___y_3392_;
v___y_3273_ = v___y_3391_;
v___y_3274_ = v___y_3393_;
v___y_3275_ = v___y_3395_;
v___y_3276_ = v___y_3396_;
v___y_3277_ = v___y_3397_;
v___y_3278_ = v___y_3398_;
v___y_3279_ = v___y_3399_;
v___y_3280_ = v___y_3400_;
v___y_3281_ = v___y_3401_;
v___y_3282_ = v___y_3402_;
v___y_3283_ = v___y_3403_;
v___y_3284_ = v___y_3418_;
v___y_3285_ = v___y_3404_;
v___y_3286_ = v___y_3405_;
v___y_3287_ = v___y_3406_;
v___y_3288_ = v___y_3407_;
v___y_3289_ = v___y_3408_;
v___y_3290_ = v___y_3409_;
v___y_3291_ = v___y_3410_;
v___y_3292_ = v___y_3411_;
v___y_3293_ = v___y_3412_;
v___y_3294_ = v___y_3413_;
v___y_3295_ = v___y_3414_;
v___y_3296_ = v___y_3415_;
v___y_3297_ = v___y_3417_;
v___y_3298_ = v___y_3416_;
v___y_3299_ = v___x_3423_;
goto v___jp_3270_;
}
else
{
if (lean_obj_tag(v___y_3418_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_dec(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3401_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3392_);
lean_dec(v___y_3390_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v___x_3424_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3425_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3424_, v___f_3388_, v___y_3391_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3433_; 
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v___x_3425_, 0);
lean_dec(v_unused_3434_);
v___x_3427_ = v___x_3425_;
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3425_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3425_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3425_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_dec_ref(v___f_3388_);
v___y_3271_ = v___y_3390_;
v___y_3272_ = v___y_3392_;
v___y_3273_ = v___y_3391_;
v___y_3274_ = v___y_3393_;
v___y_3275_ = v___y_3395_;
v___y_3276_ = v___y_3396_;
v___y_3277_ = v___y_3397_;
v___y_3278_ = v___y_3398_;
v___y_3279_ = v___y_3399_;
v___y_3280_ = v___y_3400_;
v___y_3281_ = v___y_3401_;
v___y_3282_ = v___y_3402_;
v___y_3283_ = v___y_3403_;
v___y_3284_ = v___y_3418_;
v___y_3285_ = v___y_3404_;
v___y_3286_ = v___y_3405_;
v___y_3287_ = v___y_3406_;
v___y_3288_ = v___y_3407_;
v___y_3289_ = v___y_3408_;
v___y_3290_ = v___y_3409_;
v___y_3291_ = v___y_3410_;
v___y_3292_ = v___y_3411_;
v___y_3293_ = v___y_3412_;
v___y_3294_ = v___y_3413_;
v___y_3295_ = v___y_3414_;
v___y_3296_ = v___y_3415_;
v___y_3297_ = v___y_3417_;
v___y_3298_ = v___y_3416_;
v___y_3299_ = v___y_3394_;
goto v___jp_3270_;
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v___y_3418_);
lean_dec(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3401_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3392_);
lean_dec(v___y_3390_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3443_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3419_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3419_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
v___jp_3451_:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_box(0);
v___y_3390_ = v___y_3452_;
v___y_3391_ = v___y_3454_;
v___y_3392_ = v___y_3453_;
v___y_3393_ = v___y_3455_;
v___y_3394_ = v___y_3456_;
v___y_3395_ = v___y_3457_;
v___y_3396_ = v___y_3458_;
v___y_3397_ = v___y_3459_;
v___y_3398_ = v___y_3460_;
v___y_3399_ = v___y_3461_;
v___y_3400_ = v___y_3462_;
v___y_3401_ = v___y_3463_;
v___y_3402_ = v___y_3464_;
v___y_3403_ = v___y_3465_;
v___y_3404_ = v___y_3466_;
v___y_3405_ = v___y_3467_;
v___y_3406_ = v___y_3468_;
v___y_3407_ = v___y_3469_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3471_;
v___y_3410_ = v___y_3472_;
v___y_3411_ = v___y_3473_;
v___y_3412_ = v___y_3474_;
v___y_3413_ = v___y_3476_;
v___y_3414_ = v___y_3475_;
v___y_3415_ = v___y_3477_;
v___y_3416_ = v___y_3479_;
v___y_3417_ = v___y_3478_;
v___y_3418_ = v___x_3480_;
goto v___jp_3389_;
}
v___jp_3481_:
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_box(0);
v___y_3452_ = v___y_3482_;
v___y_3453_ = v___y_3484_;
v___y_3454_ = v___y_3499_;
v___y_3455_ = v___y_3505_;
v___y_3456_ = v___y_3485_;
v___y_3457_ = v___y_3486_;
v___y_3458_ = v___y_3487_;
v___y_3459_ = v___y_3488_;
v___y_3460_ = v___y_3489_;
v___y_3461_ = v___y_3507_;
v___y_3462_ = v___y_3500_;
v___y_3463_ = v___y_3495_;
v___y_3464_ = v___y_3506_;
v___y_3465_ = v___y_3497_;
v___y_3466_ = v___y_3483_;
v___y_3467_ = v___y_3501_;
v___y_3468_ = v___y_3490_;
v___y_3469_ = v___y_3491_;
v___y_3470_ = v___y_3492_;
v___y_3471_ = v___y_3493_;
v___y_3472_ = v___y_3508_;
v___y_3473_ = v___y_3494_;
v___y_3474_ = v___y_3496_;
v___y_3475_ = v___y_3502_;
v___y_3476_ = v___x_3509_;
v___y_3477_ = v___y_3503_;
v___y_3478_ = v___y_3498_;
v___y_3479_ = v___y_3504_;
goto v___jp_3451_;
}
v___jp_3510_:
{
lean_object* v___x_3530_; 
lean_inc(v_a_2635_);
v___x_3530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2635_, v___y_3517_, v___y_3523_, v___y_3526_, v___y_3518_, v___y_3513_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc_n(v_a_3531_, 2);
lean_dec_ref_known(v___x_3530_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3532_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2630_, v_type_2547_, v_a_3531_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc_n(v_a_3533_, 2);
lean_dec_ref_known(v___x_3532_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3534_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2630_, v_type_2547_, v_a_3533_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3589_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3589_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3589_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
if (lean_obj_tag(v_a_3535_) == 1)
{
lean_object* v_val_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
lean_del_object(v___x_3537_);
v_val_3539_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_val_3539_);
lean_dec_ref_known(v_a_3535_, 1);
v___x_3540_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3540_, v_val_2630_, v_type_2547_, v___y_3513_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc_n(v_a_3542_, 2);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3544_ = lean_box(0);
lean_inc_n(v_val_2630_, 3);
v___x_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3545_, 0, v_val_2630_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v_val_2630_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
lean_inc_ref(v___x_3546_);
v___x_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_val_2630_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
lean_inc_ref(v___x_3547_);
v___x_3548_ = l_Lean_mkConst(v___x_3543_, v___x_3547_);
lean_inc_ref_n(v_type_2547_, 3);
v___x_3549_ = l_Lean_mkApp4(v___x_3548_, v_type_2547_, v_type_2547_, v_type_2547_, v_a_3542_);
v___x_3550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3549_, v___y_3513_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3550_) == 0)
{
if (lean_obj_tag(v___y_3522_) == 1)
{
if (lean_obj_tag(v___y_3520_) == 1)
{
lean_object* v_a_3551_; lean_object* v_val_3552_; lean_object* v_val_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_val_3552_ = lean_ctor_get(v___y_3522_, 0);
v_val_3553_ = lean_ctor_get(v___y_3520_, 0);
v___x_3554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v___x_3545_);
v___x_3555_ = l_Lean_mkConst(v___x_3554_, v___x_3545_);
lean_inc(v_val_3553_);
lean_inc(v_val_3552_);
lean_inc(v_a_3542_);
lean_inc_ref(v_type_2547_);
v___x_3556_ = l_Lean_mkApp4(v___x_3555_, v_type_2547_, v_a_3542_, v_val_3552_, v_val_3553_);
v___x_3557_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3556_, v___y_3515_, v___y_3528_, v___y_3524_, v___y_3527_, v___y_3525_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
if (lean_obj_tag(v_a_3558_) == 0)
{
lean_dec_ref_known(v___y_3520_, 1);
v___y_3452_ = v___y_3511_;
v___y_3453_ = v___y_3512_;
v___y_3454_ = v___y_3517_;
v___y_3455_ = v___y_3528_;
v___y_3456_ = v___y_3529_;
v___y_3457_ = v___y_3514_;
v___y_3458_ = v___y_3516_;
v___y_3459_ = v_val_3539_;
v___y_3460_ = v___x_3546_;
v___y_3461_ = v___y_3527_;
v___y_3462_ = v___y_3523_;
v___y_3463_ = v_a_3533_;
v___y_3464_ = v___y_3524_;
v___y_3465_ = v_a_3551_;
v___y_3466_ = v_a_3542_;
v___y_3467_ = v___y_3526_;
v___y_3468_ = v___x_3545_;
v___y_3469_ = v___y_3519_;
v___y_3470_ = v___y_3521_;
v___y_3471_ = v_a_3531_;
v___y_3472_ = v___y_3525_;
v___y_3473_ = v___y_3522_;
v___y_3474_ = v___x_3547_;
v___y_3475_ = v___y_3518_;
v___y_3476_ = v_a_3558_;
v___y_3477_ = v___y_3513_;
v___y_3478_ = v___x_3544_;
v___y_3479_ = v___y_3515_;
goto v___jp_3451_;
}
else
{
if (v___y_3529_ == 0)
{
v___y_3390_ = v___y_3511_;
v___y_3391_ = v___y_3517_;
v___y_3392_ = v___y_3512_;
v___y_3393_ = v___y_3528_;
v___y_3394_ = v___y_3529_;
v___y_3395_ = v___y_3514_;
v___y_3396_ = v___y_3516_;
v___y_3397_ = v_val_3539_;
v___y_3398_ = v___x_3546_;
v___y_3399_ = v___y_3527_;
v___y_3400_ = v___y_3523_;
v___y_3401_ = v_a_3533_;
v___y_3402_ = v___y_3524_;
v___y_3403_ = v_a_3551_;
v___y_3404_ = v_a_3542_;
v___y_3405_ = v___y_3526_;
v___y_3406_ = v___x_3545_;
v___y_3407_ = v___y_3519_;
v___y_3408_ = v___y_3521_;
v___y_3409_ = v_a_3531_;
v___y_3410_ = v___y_3525_;
v___y_3411_ = v___y_3522_;
v___y_3412_ = v___x_3547_;
v___y_3413_ = v_a_3558_;
v___y_3414_ = v___y_3518_;
v___y_3415_ = v___y_3513_;
v___y_3416_ = v___y_3515_;
v___y_3417_ = v___x_3544_;
v___y_3418_ = v___y_3520_;
goto v___jp_3389_;
}
else
{
lean_dec_ref_known(v___y_3520_, 1);
v___y_3452_ = v___y_3511_;
v___y_3453_ = v___y_3512_;
v___y_3454_ = v___y_3517_;
v___y_3455_ = v___y_3528_;
v___y_3456_ = v___y_3529_;
v___y_3457_ = v___y_3514_;
v___y_3458_ = v___y_3516_;
v___y_3459_ = v_val_3539_;
v___y_3460_ = v___x_3546_;
v___y_3461_ = v___y_3527_;
v___y_3462_ = v___y_3523_;
v___y_3463_ = v_a_3533_;
v___y_3464_ = v___y_3524_;
v___y_3465_ = v_a_3551_;
v___y_3466_ = v_a_3542_;
v___y_3467_ = v___y_3526_;
v___y_3468_ = v___x_3545_;
v___y_3469_ = v___y_3519_;
v___y_3470_ = v___y_3521_;
v___y_3471_ = v_a_3531_;
v___y_3472_ = v___y_3525_;
v___y_3473_ = v___y_3522_;
v___y_3474_ = v___x_3547_;
v___y_3475_ = v___y_3518_;
v___y_3476_ = v_a_3558_;
v___y_3477_ = v___y_3513_;
v___y_3478_ = v___x_3544_;
v___y_3479_ = v___y_3515_;
goto v___jp_3451_;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3551_);
lean_dec_ref_known(v___y_3520_, 1);
lean_dec_ref_known(v___y_3522_, 1);
lean_dec_ref_known(v___x_3547_, 2);
lean_dec_ref_known(v___x_3546_, 2);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3542_);
lean_dec(v_val_3539_);
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
lean_dec(v___y_3521_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3559_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3557_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3557_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; 
lean_dec(v___y_3520_);
v_a_3567_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3482_ = v___y_3511_;
v___y_3483_ = v_a_3542_;
v___y_3484_ = v___y_3512_;
v___y_3485_ = v___y_3529_;
v___y_3486_ = v___y_3514_;
v___y_3487_ = v___y_3516_;
v___y_3488_ = v_val_3539_;
v___y_3489_ = v___x_3546_;
v___y_3490_ = v___x_3545_;
v___y_3491_ = v___y_3519_;
v___y_3492_ = v___y_3521_;
v___y_3493_ = v_a_3531_;
v___y_3494_ = v___y_3522_;
v___y_3495_ = v_a_3533_;
v___y_3496_ = v___x_3547_;
v___y_3497_ = v_a_3567_;
v___y_3498_ = v___x_3544_;
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3523_;
v___y_3501_ = v___y_3526_;
v___y_3502_ = v___y_3518_;
v___y_3503_ = v___y_3513_;
v___y_3504_ = v___y_3515_;
v___y_3505_ = v___y_3528_;
v___y_3506_ = v___y_3524_;
v___y_3507_ = v___y_3527_;
v___y_3508_ = v___y_3525_;
goto v___jp_3481_;
}
}
else
{
lean_object* v_a_3568_; 
lean_dec(v___y_3520_);
v_a_3568_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3482_ = v___y_3511_;
v___y_3483_ = v_a_3542_;
v___y_3484_ = v___y_3512_;
v___y_3485_ = v___y_3529_;
v___y_3486_ = v___y_3514_;
v___y_3487_ = v___y_3516_;
v___y_3488_ = v_val_3539_;
v___y_3489_ = v___x_3546_;
v___y_3490_ = v___x_3545_;
v___y_3491_ = v___y_3519_;
v___y_3492_ = v___y_3521_;
v___y_3493_ = v_a_3531_;
v___y_3494_ = v___y_3522_;
v___y_3495_ = v_a_3533_;
v___y_3496_ = v___x_3547_;
v___y_3497_ = v_a_3568_;
v___y_3498_ = v___x_3544_;
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3523_;
v___y_3501_ = v___y_3526_;
v___y_3502_ = v___y_3518_;
v___y_3503_ = v___y_3513_;
v___y_3504_ = v___y_3515_;
v___y_3505_ = v___y_3528_;
v___y_3506_ = v___y_3524_;
v___y_3507_ = v___y_3527_;
v___y_3508_ = v___y_3525_;
goto v___jp_3481_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref_known(v___x_3547_, 2);
lean_dec_ref_known(v___x_3546_, 2);
lean_dec_ref_known(v___x_3545_, 2);
lean_dec(v_a_3542_);
lean_dec(v_val_3539_);
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3569_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3550_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3550_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_val_3539_);
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3577_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3541_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3541_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
lean_dec(v_a_3535_);
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v___x_3585_ = lean_box(0);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3585_);
v___x_3587_ = v___x_3537_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_a_3533_);
lean_dec(v_a_3531_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3590_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3534_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3534_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec(v_a_3531_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3598_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3532_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3532_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3606_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3530_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3530_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
v___jp_3614_:
{
lean_object* v___x_3633_; 
lean_inc(v___y_3618_);
lean_inc_ref(v_type_2547_);
v___x_3633_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_____do__lift_3622_, v_type_2547_, v___y_3618_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3625_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; uint8_t v_ring_3637_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref_known(v___x_3635_, 1);
v_ring_3637_ = lean_ctor_get_uint8(v_a_3636_, sizeof(void*)*14 + 21);
lean_dec(v_a_3636_);
if (v_ring_3637_ == 0)
{
v___y_3511_ = v___y_3615_;
v___y_3512_ = v___y_3617_;
v___y_3513_ = v___y_3627_;
v___y_3514_ = v___y_3619_;
v___y_3515_ = v___y_3628_;
v___y_3516_ = v___y_3620_;
v___y_3517_ = v___y_3623_;
v___y_3518_ = v___y_3626_;
v___y_3519_ = v___y_3621_;
v___y_3520_ = v___y_3616_;
v___y_3521_ = v_a_3634_;
v___y_3522_ = v___y_3618_;
v___y_3523_ = v___y_3624_;
v___y_3524_ = v___y_3630_;
v___y_3525_ = v___y_3632_;
v___y_3526_ = v___y_3625_;
v___y_3527_ = v___y_3631_;
v___y_3528_ = v___y_3629_;
v___y_3529_ = v_ring_3637_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = lean_box(0);
v___x_3639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2635_, v___x_3638_);
if (v___x_3639_ == 0)
{
v___y_3511_ = v___y_3615_;
v___y_3512_ = v___y_3617_;
v___y_3513_ = v___y_3627_;
v___y_3514_ = v___y_3619_;
v___y_3515_ = v___y_3628_;
v___y_3516_ = v___y_3620_;
v___y_3517_ = v___y_3623_;
v___y_3518_ = v___y_3626_;
v___y_3519_ = v___y_3621_;
v___y_3520_ = v___y_3616_;
v___y_3521_ = v_a_3634_;
v___y_3522_ = v___y_3618_;
v___y_3523_ = v___y_3624_;
v___y_3524_ = v___y_3630_;
v___y_3525_ = v___y_3632_;
v___y_3526_ = v___y_3625_;
v___y_3527_ = v___y_3631_;
v___y_3528_ = v___y_3629_;
v___y_3529_ = v___x_3639_;
goto v___jp_3510_;
}
else
{
if (lean_obj_tag(v___y_3616_) == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_a_3634_);
lean_dec(v___y_3621_);
lean_dec(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec(v___y_3615_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v___x_3640_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3641_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3640_, v___f_3388_, v___y_3623_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3649_; 
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v___x_3641_, 0);
lean_dec(v_unused_3650_);
v___x_3643_ = v___x_3641_;
v_isShared_3644_ = v_isSharedCheck_3649_;
goto v_resetjp_3642_;
}
else
{
lean_dec(v___x_3641_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3649_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = lean_box(0);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3645_);
v___x_3647_ = v___x_3643_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
v_a_3651_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3641_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3641_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
uint8_t v___x_3659_; 
v___x_3659_ = 0;
v___y_3511_ = v___y_3615_;
v___y_3512_ = v___y_3617_;
v___y_3513_ = v___y_3627_;
v___y_3514_ = v___y_3619_;
v___y_3515_ = v___y_3628_;
v___y_3516_ = v___y_3620_;
v___y_3517_ = v___y_3623_;
v___y_3518_ = v___y_3626_;
v___y_3519_ = v___y_3621_;
v___y_3520_ = v___y_3616_;
v___y_3521_ = v_a_3634_;
v___y_3522_ = v___y_3618_;
v___y_3523_ = v___y_3624_;
v___y_3524_ = v___y_3630_;
v___y_3525_ = v___y_3632_;
v___y_3526_ = v___y_3625_;
v___y_3527_ = v___y_3631_;
v___y_3528_ = v___y_3629_;
v___y_3529_ = v___x_3659_;
goto v___jp_3510_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_a_3634_);
lean_dec(v___y_3621_);
lean_dec(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3660_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3635_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3635_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v___y_3621_);
lean_dec(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3668_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3633_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3633_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
v___jp_3676_:
{
lean_object* v___x_3694_; 
lean_inc(v___y_3679_);
lean_inc_ref(v_type_2547_);
v___x_3694_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_____do__lift_3683_, v_type_2547_, v___y_3679_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___x_3696_ = l_Lean_leCarrierIsSort(v___y_3692_, v___y_3693_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; uint8_t v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
v___x_3698_ = lean_unbox(v_a_3697_);
lean_dec(v_a_3697_);
if (v___x_3698_ == 0)
{
lean_inc(v_val_2630_);
v___y_3615_ = v___y_3677_;
v___y_3616_ = v___y_3678_;
v___y_3617_ = v_a_3695_;
v___y_3618_ = v___y_3679_;
v___y_3619_ = v___y_3680_;
v___y_3620_ = v___y_3681_;
v___y_3621_ = v___y_3682_;
v_____do__lift_3622_ = v_val_2630_;
v___y_3623_ = v___y_3684_;
v___y_3624_ = v___y_3685_;
v___y_3625_ = v___y_3686_;
v___y_3626_ = v___y_3687_;
v___y_3627_ = v___y_3688_;
v___y_3628_ = v___y_3689_;
v___y_3629_ = v___y_3690_;
v___y_3630_ = v___y_3691_;
v___y_3631_ = v___y_3692_;
v___y_3632_ = v___y_3693_;
goto v___jp_3614_;
}
else
{
lean_object* v___x_3699_; 
lean_inc(v_val_2630_);
v___x_3699_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_3615_ = v___y_3677_;
v___y_3616_ = v___y_3678_;
v___y_3617_ = v_a_3695_;
v___y_3618_ = v___y_3679_;
v___y_3619_ = v___y_3680_;
v___y_3620_ = v___y_3681_;
v___y_3621_ = v___y_3682_;
v_____do__lift_3622_ = v___x_3699_;
v___y_3623_ = v___y_3684_;
v___y_3624_ = v___y_3685_;
v___y_3625_ = v___y_3686_;
v___y_3626_ = v___y_3687_;
v___y_3627_ = v___y_3688_;
v___y_3628_ = v___y_3689_;
v___y_3629_ = v___y_3690_;
v___y_3630_ = v___y_3691_;
v___y_3631_ = v___y_3692_;
v___y_3632_ = v___y_3693_;
goto v___jp_3614_;
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_a_3695_);
lean_dec(v___y_3682_);
lean_dec(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3700_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3696_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3696_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v___y_3682_);
lean_dec(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3708_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3694_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3694_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
v___jp_3716_:
{
lean_object* v___x_3733_; 
lean_inc(v___y_3718_);
lean_inc_ref(v_type_2547_);
v___x_3733_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_____do__lift_3722_, v_type_2547_, v___y_3718_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l_Lean_leCarrierIsSort(v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; uint8_t v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3737_ = lean_unbox(v_a_3736_);
lean_dec(v_a_3736_);
if (v___x_3737_ == 0)
{
lean_inc(v_val_2630_);
v___y_3677_ = v___y_3717_;
v___y_3678_ = v_a_3734_;
v___y_3679_ = v___y_3718_;
v___y_3680_ = v___y_3719_;
v___y_3681_ = v___y_3720_;
v___y_3682_ = v___y_3721_;
v_____do__lift_3683_ = v_val_2630_;
v___y_3684_ = v___y_3723_;
v___y_3685_ = v___y_3724_;
v___y_3686_ = v___y_3725_;
v___y_3687_ = v___y_3726_;
v___y_3688_ = v___y_3727_;
v___y_3689_ = v___y_3728_;
v___y_3690_ = v___y_3729_;
v___y_3691_ = v___y_3730_;
v___y_3692_ = v___y_3731_;
v___y_3693_ = v___y_3732_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3738_; 
lean_inc(v_val_2630_);
v___x_3738_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_3677_ = v___y_3717_;
v___y_3678_ = v_a_3734_;
v___y_3679_ = v___y_3718_;
v___y_3680_ = v___y_3719_;
v___y_3681_ = v___y_3720_;
v___y_3682_ = v___y_3721_;
v_____do__lift_3683_ = v___x_3738_;
v___y_3684_ = v___y_3723_;
v___y_3685_ = v___y_3724_;
v___y_3686_ = v___y_3725_;
v___y_3687_ = v___y_3726_;
v___y_3688_ = v___y_3727_;
v___y_3689_ = v___y_3728_;
v___y_3690_ = v___y_3729_;
v___y_3691_ = v___y_3730_;
v___y_3692_ = v___y_3731_;
v___y_3693_ = v___y_3732_;
goto v___jp_3676_;
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_a_3734_);
lean_dec(v___y_3721_);
lean_dec(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3739_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3735_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3735_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v___y_3721_);
lean_dec(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3747_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3733_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3733_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
v___jp_3755_:
{
lean_object* v___x_3771_; 
lean_inc(v___y_3757_);
lean_inc(v___y_3756_);
lean_inc_ref(v_type_2547_);
v___x_3771_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_____do__lift_3760_, v_type_2547_, v___y_3756_, v___y_3757_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l_Lean_leCarrierIsSort(v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; uint8_t v___x_3775_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3775_ = lean_unbox(v_a_3774_);
lean_dec(v_a_3774_);
if (v___x_3775_ == 0)
{
lean_inc(v_val_2630_);
v___y_3717_ = v___y_3756_;
v___y_3718_ = v___y_3757_;
v___y_3719_ = v___y_3758_;
v___y_3720_ = v___y_3759_;
v___y_3721_ = v_a_3772_;
v_____do__lift_3722_ = v_val_2630_;
v___y_3723_ = v___y_3761_;
v___y_3724_ = v___y_3762_;
v___y_3725_ = v___y_3763_;
v___y_3726_ = v___y_3764_;
v___y_3727_ = v___y_3765_;
v___y_3728_ = v___y_3766_;
v___y_3729_ = v___y_3767_;
v___y_3730_ = v___y_3768_;
v___y_3731_ = v___y_3769_;
v___y_3732_ = v___y_3770_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3776_; 
lean_inc(v_val_2630_);
v___x_3776_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_3717_ = v___y_3756_;
v___y_3718_ = v___y_3757_;
v___y_3719_ = v___y_3758_;
v___y_3720_ = v___y_3759_;
v___y_3721_ = v_a_3772_;
v_____do__lift_3722_ = v___x_3776_;
v___y_3723_ = v___y_3761_;
v___y_3724_ = v___y_3762_;
v___y_3725_ = v___y_3763_;
v___y_3726_ = v___y_3764_;
v___y_3727_ = v___y_3765_;
v___y_3728_ = v___y_3766_;
v___y_3729_ = v___y_3767_;
v___y_3730_ = v___y_3768_;
v___y_3731_ = v___y_3769_;
v___y_3732_ = v___y_3770_;
goto v___jp_3716_;
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_a_3772_);
lean_dec(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3777_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3773_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3773_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3785_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3771_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3771_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
v___jp_3793_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2547_);
v___x_3809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3808_, v_____do__lift_3796_, v_type_2547_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l_Lean_leCarrierIsSort(v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; uint8_t v___x_3813_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = lean_unbox(v_a_3812_);
lean_dec(v_a_3812_);
if (v___x_3813_ == 0)
{
lean_inc(v_val_2630_);
v___y_3756_ = v_a_3810_;
v___y_3757_ = v___y_3794_;
v___y_3758_ = v___y_3795_;
v___y_3759_ = v___x_3807_;
v_____do__lift_3760_ = v_val_2630_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
v___y_3765_ = v___y_3801_;
v___y_3766_ = v___y_3802_;
v___y_3767_ = v___y_3803_;
v___y_3768_ = v___y_3804_;
v___y_3769_ = v___y_3805_;
v___y_3770_ = v___y_3806_;
goto v___jp_3755_;
}
else
{
lean_object* v___x_3814_; 
lean_inc(v_val_2630_);
v___x_3814_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_3756_ = v_a_3810_;
v___y_3757_ = v___y_3794_;
v___y_3758_ = v___y_3795_;
v___y_3759_ = v___x_3807_;
v_____do__lift_3760_ = v___x_3814_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
v___y_3765_ = v___y_3801_;
v___y_3766_ = v___y_3802_;
v___y_3767_ = v___y_3803_;
v___y_3768_ = v___y_3804_;
v___y_3769_ = v___y_3805_;
v___y_3770_ = v___y_3806_;
goto v___jp_3755_;
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_a_3810_);
lean_dec(v___y_3794_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3815_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3811_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3811_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec(v___y_3794_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3823_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3809_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3809_);
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
v___jp_3831_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
v___x_3844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_type_2547_);
v___x_3845_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3844_, v_____do__lift_3832_, v_type_2547_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = l_Lean_leCarrierIsSort(v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; uint8_t v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_unbox(v_a_3848_);
lean_dec(v_a_3848_);
if (v___x_3849_ == 0)
{
lean_inc(v_val_2630_);
v___y_3794_ = v_a_3846_;
v___y_3795_ = v___x_3843_;
v_____do__lift_3796_ = v_val_2630_;
v___y_3797_ = v___y_3833_;
v___y_3798_ = v___y_3834_;
v___y_3799_ = v___y_3835_;
v___y_3800_ = v___y_3836_;
v___y_3801_ = v___y_3837_;
v___y_3802_ = v___y_3838_;
v___y_3803_ = v___y_3839_;
v___y_3804_ = v___y_3840_;
v___y_3805_ = v___y_3841_;
v___y_3806_ = v___y_3842_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3850_; 
lean_inc(v_val_2630_);
v___x_3850_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_3794_ = v_a_3846_;
v___y_3795_ = v___x_3843_;
v_____do__lift_3796_ = v___x_3850_;
v___y_3797_ = v___y_3833_;
v___y_3798_ = v___y_3834_;
v___y_3799_ = v___y_3835_;
v___y_3800_ = v___y_3836_;
v___y_3801_ = v___y_3837_;
v___y_3802_ = v___y_3838_;
v___y_3803_ = v___y_3839_;
v___y_3804_ = v___y_3840_;
v___y_3805_ = v___y_3841_;
v___y_3806_ = v___y_3842_;
goto v___jp_3793_;
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_a_3846_);
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3851_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3847_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3847_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v___f_3388_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3859_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3845_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3845_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3869_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3386_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3386_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
v___jp_2639_:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2668_, v___y_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_structs_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_structs_2680_ = lean_ctor_get(v_a_2679_, 0);
lean_inc_ref(v_structs_2680_);
lean_dec(v_a_2679_);
v___x_2681_ = lean_array_get_size(v_structs_2680_);
lean_dec_ref(v_structs_2680_);
v___x_2682_ = lean_unsigned_to_nat(32u);
v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0);
v___x_2685_ = ((size_t)5ULL);
lean_inc(v___y_2647_);
v___x_2686_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2683_);
lean_ctor_set(v___x_2686_, 2, v___y_2647_);
lean_ctor_set(v___x_2686_, 3, v___y_2647_);
lean_ctor_set_usize(v___x_2686_, 4, v___x_2685_);
v___x_2687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2);
v___x_2688_ = lean_box(0);
v___x_2689_ = lean_box(0);
lean_inc_ref_n(v___x_2686_, 7);
lean_inc(v___y_2644_);
lean_inc(v___y_2656_);
lean_inc(v___y_2666_);
lean_inc(v___y_2654_);
lean_inc(v___y_2646_);
v___x_2690_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2690_, 0, v___x_2681_);
lean_ctor_set(v___x_2690_, 1, v_a_2635_);
lean_ctor_set(v___x_2690_, 2, v_type_2547_);
lean_ctor_set(v___x_2690_, 3, v_val_2630_);
lean_ctor_set(v___x_2690_, 4, v___y_2642_);
lean_ctor_set(v___x_2690_, 5, v___y_2661_);
lean_ctor_set(v___x_2690_, 6, v___y_2640_);
lean_ctor_set(v___x_2690_, 7, v___y_2657_);
lean_ctor_set(v___x_2690_, 8, v___y_2652_);
lean_ctor_set(v___x_2690_, 9, v___y_2662_);
lean_ctor_set(v___x_2690_, 10, v___y_2651_);
lean_ctor_set(v___x_2690_, 11, v___y_2660_);
lean_ctor_set(v___x_2690_, 12, v___y_2646_);
lean_ctor_set(v___x_2690_, 13, v___y_2659_);
lean_ctor_set(v___x_2690_, 14, v___y_2654_);
lean_ctor_set(v___x_2690_, 15, v___y_2666_);
lean_ctor_set(v___x_2690_, 16, v___y_2656_);
lean_ctor_set(v___x_2690_, 17, v___y_2663_);
lean_ctor_set(v___x_2690_, 18, v___y_2648_);
lean_ctor_set(v___x_2690_, 19, v___y_2644_);
lean_ctor_set(v___x_2690_, 20, v___y_2664_);
lean_ctor_set(v___x_2690_, 21, v___y_2655_);
lean_ctor_set(v___x_2690_, 22, v___y_2650_);
lean_ctor_set(v___x_2690_, 23, v___y_2658_);
lean_ctor_set(v___x_2690_, 24, v___y_2641_);
lean_ctor_set(v___x_2690_, 25, v___y_2649_);
lean_ctor_set(v___x_2690_, 26, v___y_2645_);
lean_ctor_set(v___x_2690_, 27, v_homomulFn_x3f_2667_);
lean_ctor_set(v___x_2690_, 28, v___y_2665_);
lean_ctor_set(v___x_2690_, 29, v___y_2653_);
lean_ctor_set(v___x_2690_, 30, v___x_2686_);
lean_ctor_set(v___x_2690_, 31, v___x_2687_);
lean_ctor_set(v___x_2690_, 32, v___x_2686_);
lean_ctor_set(v___x_2690_, 33, v___x_2686_);
lean_ctor_set(v___x_2690_, 34, v___x_2686_);
lean_ctor_set(v___x_2690_, 35, v___x_2686_);
lean_ctor_set(v___x_2690_, 36, v___x_2688_);
lean_ctor_set(v___x_2690_, 37, v___x_2687_);
lean_ctor_set(v___x_2690_, 38, v___x_2686_);
lean_ctor_set(v___x_2690_, 39, v___x_2689_);
lean_ctor_set(v___x_2690_, 40, v___x_2686_);
lean_ctor_set(v___x_2690_, 41, v___x_2686_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*42, v___y_2643_);
v___f_2691_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2691_, 0, v___x_2690_);
v___x_2692_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2692_, v___f_2691_, v___y_2668_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref_known(v___x_2693_, 1);
if (lean_obj_tag(v___y_2644_) == 1)
{
if (lean_obj_tag(v___y_2646_) == 0)
{
lean_dec_ref_known(v___y_2644_, 1);
lean_dec(v___y_2666_);
lean_dec(v___y_2656_);
lean_dec(v___y_2654_);
v___y_2560_ = v___x_2681_;
goto v___jp_2559_;
}
else
{
lean_dec_ref_known(v___y_2646_, 1);
if (lean_obj_tag(v___y_2654_) == 0)
{
if (v___y_2643_ == 0)
{
if (lean_obj_tag(v___y_2666_) == 0)
{
lean_object* v_val_2694_; uint8_t v___x_2695_; 
v_val_2694_ = lean_ctor_get(v___y_2644_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v___y_2644_, 1);
v___x_2695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2656_);
lean_dec(v___y_2656_);
if (v___x_2695_ == 0)
{
lean_dec(v_val_2694_);
v___y_2560_ = v___x_2681_;
goto v___jp_2559_;
}
else
{
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2675_;
v___y_2603_ = v___y_2676_;
v___y_2604_ = v___y_2674_;
v___y_2605_ = v___y_2669_;
v___y_2606_ = v___y_2643_;
v___y_2607_ = v___y_2671_;
v___y_2608_ = v___y_2672_;
v___y_2609_ = v_val_2694_;
v___y_2610_ = v___y_2668_;
v___y_2611_ = v___x_2681_;
v___y_2612_ = v___y_2670_;
v___y_2613_ = v___y_2677_;
goto v___jp_2600_;
}
}
else
{
lean_object* v_val_2696_; 
lean_dec_ref_known(v___y_2666_, 1);
lean_dec(v___y_2656_);
v_val_2696_ = lean_ctor_get(v___y_2644_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v___y_2644_, 1);
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2675_;
v___y_2603_ = v___y_2676_;
v___y_2604_ = v___y_2674_;
v___y_2605_ = v___y_2669_;
v___y_2606_ = v___y_2643_;
v___y_2607_ = v___y_2671_;
v___y_2608_ = v___y_2672_;
v___y_2609_ = v_val_2696_;
v___y_2610_ = v___y_2668_;
v___y_2611_ = v___x_2681_;
v___y_2612_ = v___y_2670_;
v___y_2613_ = v___y_2677_;
goto v___jp_2600_;
}
}
else
{
lean_object* v_val_2697_; 
lean_dec(v___y_2666_);
lean_dec(v___y_2656_);
v_val_2697_ = lean_ctor_get(v___y_2644_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v___y_2644_, 1);
v___y_2575_ = v___y_2673_;
v___y_2576_ = v___y_2675_;
v___y_2577_ = v___y_2676_;
v___y_2578_ = v___y_2674_;
v___y_2579_ = v___y_2669_;
v___y_2580_ = v___y_2643_;
v___y_2581_ = v___y_2671_;
v___y_2582_ = v___y_2672_;
v___y_2583_ = v_val_2697_;
v___y_2584_ = v___y_2668_;
v___y_2585_ = v___x_2681_;
v___y_2586_ = v___y_2670_;
v___y_2587_ = v___y_2677_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_val_2698_; 
lean_dec_ref_known(v___y_2654_, 1);
lean_dec(v___y_2666_);
lean_dec(v___y_2656_);
v_val_2698_ = lean_ctor_get(v___y_2644_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v___y_2644_, 1);
v___y_2575_ = v___y_2673_;
v___y_2576_ = v___y_2675_;
v___y_2577_ = v___y_2676_;
v___y_2578_ = v___y_2674_;
v___y_2579_ = v___y_2669_;
v___y_2580_ = v___y_2643_;
v___y_2581_ = v___y_2671_;
v___y_2582_ = v___y_2672_;
v___y_2583_ = v_val_2698_;
v___y_2584_ = v___y_2668_;
v___y_2585_ = v___x_2681_;
v___y_2586_ = v___y_2670_;
v___y_2587_ = v___y_2677_;
goto v___jp_2574_;
}
}
}
else
{
lean_dec(v___y_2666_);
lean_dec(v___y_2656_);
lean_dec(v___y_2654_);
lean_dec(v___y_2646_);
lean_dec(v___y_2644_);
v___y_2560_ = v___x_2681_;
goto v___jp_2559_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v___y_2666_);
lean_dec(v___y_2656_);
lean_dec(v___y_2654_);
lean_dec(v___y_2646_);
lean_dec(v___y_2644_);
v_a_2699_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2693_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2693_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_homomulFn_x3f_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v_a_2635_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2707_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2678_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2678_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
v___jp_2715_:
{
lean_object* v___x_2753_; 
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_2753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2630_, v_type_2547_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_2755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2630_, v_type_2547_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2755_) == 0)
{
if (lean_obj_tag(v___y_2733_) == 0)
{
lean_object* v_a_2756_; 
lean_dec(v___y_2736_);
lean_del_object(v___x_2632_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v___y_2640_ = v___y_2716_;
v___y_2641_ = v___y_2717_;
v___y_2642_ = v___y_2718_;
v___y_2643_ = v___y_2720_;
v___y_2644_ = v___y_2719_;
v___y_2645_ = v_a_2756_;
v___y_2646_ = v___y_2721_;
v___y_2647_ = v___y_2723_;
v___y_2648_ = v___y_2722_;
v___y_2649_ = v_a_2754_;
v___y_2650_ = v___y_2724_;
v___y_2651_ = v___y_2727_;
v___y_2652_ = v___y_2726_;
v___y_2653_ = v___y_2728_;
v___y_2654_ = v___y_2729_;
v___y_2655_ = v_ltFn_x3f_2742_;
v___y_2656_ = v___y_2730_;
v___y_2657_ = v___y_2731_;
v___y_2658_ = v___y_2732_;
v___y_2659_ = v___y_2733_;
v___y_2660_ = v___y_2734_;
v___y_2661_ = v___y_2735_;
v___y_2662_ = v___y_2737_;
v___y_2663_ = v___y_2738_;
v___y_2664_ = v___y_2739_;
v___y_2665_ = v___y_2740_;
v___y_2666_ = v___y_2741_;
v_homomulFn_x3f_2667_ = v___y_2725_;
v___y_2668_ = v___y_2743_;
v___y_2669_ = v___y_2744_;
v___y_2670_ = v___y_2745_;
v___y_2671_ = v___y_2746_;
v___y_2672_ = v___y_2747_;
v___y_2673_ = v___y_2748_;
v___y_2674_ = v___y_2749_;
v___y_2675_ = v___y_2750_;
v___y_2676_ = v___y_2751_;
v___y_2677_ = v___y_2752_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec(v___y_2725_);
v_a_2757_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_2759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2758_, v_val_2630_, v_type_2547_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6));
v___x_2762_ = l_Lean_mkConst(v___x_2761_, v___y_2736_);
lean_inc_ref_n(v_type_2547_, 3);
v___x_2763_ = l_Lean_mkApp4(v___x_2762_, v_type_2547_, v_type_2547_, v_type_2547_, v_a_2760_);
v___x_2764_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2763_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v_a_2765_);
v___x_2767_ = v___x_2632_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
v___y_2640_ = v___y_2716_;
v___y_2641_ = v___y_2717_;
v___y_2642_ = v___y_2718_;
v___y_2643_ = v___y_2720_;
v___y_2644_ = v___y_2719_;
v___y_2645_ = v_a_2757_;
v___y_2646_ = v___y_2721_;
v___y_2647_ = v___y_2723_;
v___y_2648_ = v___y_2722_;
v___y_2649_ = v_a_2754_;
v___y_2650_ = v___y_2724_;
v___y_2651_ = v___y_2727_;
v___y_2652_ = v___y_2726_;
v___y_2653_ = v___y_2728_;
v___y_2654_ = v___y_2729_;
v___y_2655_ = v_ltFn_x3f_2742_;
v___y_2656_ = v___y_2730_;
v___y_2657_ = v___y_2731_;
v___y_2658_ = v___y_2732_;
v___y_2659_ = v___y_2733_;
v___y_2660_ = v___y_2734_;
v___y_2661_ = v___y_2735_;
v___y_2662_ = v___y_2737_;
v___y_2663_ = v___y_2738_;
v___y_2664_ = v___y_2739_;
v___y_2665_ = v___y_2740_;
v___y_2666_ = v___y_2741_;
v_homomulFn_x3f_2667_ = v___x_2767_;
v___y_2668_ = v___y_2743_;
v___y_2669_ = v___y_2744_;
v___y_2670_ = v___y_2745_;
v___y_2671_ = v___y_2746_;
v___y_2672_ = v___y_2747_;
v___y_2673_ = v___y_2748_;
v___y_2674_ = v___y_2749_;
v___y_2675_ = v___y_2750_;
v___y_2676_ = v___y_2751_;
v___y_2677_ = v___y_2752_;
goto v___jp_2639_;
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2757_);
lean_dec_ref_known(v___y_2733_, 1);
lean_dec(v_a_2754_);
lean_dec(v_ltFn_x3f_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2769_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2764_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2764_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2757_);
lean_dec_ref_known(v___y_2733_, 1);
lean_dec(v_a_2754_);
lean_dec(v_ltFn_x3f_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2777_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2759_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2759_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_a_2754_);
lean_dec(v_ltFn_x3f_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2785_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2755_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2755_);
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
lean_dec(v_ltFn_x3f_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2793_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2753_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2753_);
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
v___jp_2801_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7));
lean_inc_ref(v___y_2804_);
v___x_2843_ = l_Lean_Name_mkStr2(v___y_2804_, v___x_2842_);
lean_inc(v___y_2830_);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_____do__lift_2831_);
lean_ctor_set(v___x_2844_, 1, v___y_2830_);
v___x_2845_ = l_Lean_mkConst(v___x_2843_, v___x_2844_);
lean_inc_ref(v_type_2547_);
v___x_2846_ = l_Lean_mkAppB(v___x_2845_, v_type_2547_, v___y_2818_);
v___x_2847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2846_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
lean_ctor_set(v___x_2637_, 0, v_a_2848_);
v___x_2850_ = v___x_2637_;
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
v___y_2716_ = v___y_2802_;
v___y_2717_ = v___y_2803_;
v___y_2718_ = v___y_2805_;
v___y_2719_ = v___y_2807_;
v___y_2720_ = v___y_2806_;
v___y_2721_ = v___y_2808_;
v___y_2722_ = v___y_2810_;
v___y_2723_ = v___y_2809_;
v___y_2724_ = v___y_2812_;
v___y_2725_ = v___y_2811_;
v___y_2726_ = v___y_2813_;
v___y_2727_ = v___y_2814_;
v___y_2728_ = v___y_2815_;
v___y_2729_ = v___y_2816_;
v___y_2730_ = v___y_2817_;
v___y_2731_ = v___y_2819_;
v___y_2732_ = v___y_2820_;
v___y_2733_ = v___y_2821_;
v___y_2734_ = v___y_2822_;
v___y_2735_ = v___y_2823_;
v___y_2736_ = v___y_2824_;
v___y_2737_ = v___y_2825_;
v___y_2738_ = v___y_2828_;
v___y_2739_ = v___y_2827_;
v___y_2740_ = v___y_2826_;
v___y_2741_ = v___y_2829_;
v_ltFn_x3f_2742_ = v___x_2850_;
v___y_2743_ = v___y_2832_;
v___y_2744_ = v___y_2833_;
v___y_2745_ = v___y_2834_;
v___y_2746_ = v___y_2835_;
v___y_2747_ = v___y_2836_;
v___y_2748_ = v___y_2837_;
v___y_2749_ = v___y_2838_;
v___y_2750_ = v___y_2839_;
v___y_2751_ = v___y_2840_;
v___y_2752_ = v___y_2841_;
goto v___jp_2715_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
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
v___jp_2860_:
{
if (lean_obj_tag(v___y_2861_) == 1)
{
lean_object* v_val_2899_; lean_object* v___x_2900_; 
v_val_2899_ = lean_ctor_get(v___y_2861_, 0);
lean_inc(v_val_2899_);
v___x_2900_ = l_Lean_leCarrierIsSort(v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; uint8_t v___x_2902_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = lean_unbox(v_a_2901_);
lean_dec(v_a_2901_);
if (v___x_2902_ == 0)
{
lean_inc(v_val_2630_);
v___y_2802_ = v___y_2861_;
v___y_2803_ = v___y_2862_;
v___y_2804_ = v___y_2863_;
v___y_2805_ = v___y_2864_;
v___y_2806_ = v___y_2865_;
v___y_2807_ = v___y_2866_;
v___y_2808_ = v___y_2867_;
v___y_2809_ = v___y_2868_;
v___y_2810_ = v___y_2869_;
v___y_2811_ = v___y_2870_;
v___y_2812_ = v___y_2871_;
v___y_2813_ = v___y_2873_;
v___y_2814_ = v___y_2872_;
v___y_2815_ = v___y_2874_;
v___y_2816_ = v___y_2875_;
v___y_2817_ = v___y_2876_;
v___y_2818_ = v_val_2899_;
v___y_2819_ = v___y_2877_;
v___y_2820_ = v___y_2878_;
v___y_2821_ = v___y_2879_;
v___y_2822_ = v___y_2880_;
v___y_2823_ = v___y_2881_;
v___y_2824_ = v___y_2882_;
v___y_2825_ = v___y_2883_;
v___y_2826_ = v___y_2885_;
v___y_2827_ = v_leFn_x3f_2888_;
v___y_2828_ = v___y_2884_;
v___y_2829_ = v___y_2887_;
v___y_2830_ = v___y_2886_;
v_____do__lift_2831_ = v_val_2630_;
v___y_2832_ = v___y_2889_;
v___y_2833_ = v___y_2890_;
v___y_2834_ = v___y_2891_;
v___y_2835_ = v___y_2892_;
v___y_2836_ = v___y_2893_;
v___y_2837_ = v___y_2894_;
v___y_2838_ = v___y_2895_;
v___y_2839_ = v___y_2896_;
v___y_2840_ = v___y_2897_;
v___y_2841_ = v___y_2898_;
goto v___jp_2801_;
}
else
{
lean_object* v___x_2903_; 
lean_inc(v_val_2630_);
v___x_2903_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_2802_ = v___y_2861_;
v___y_2803_ = v___y_2862_;
v___y_2804_ = v___y_2863_;
v___y_2805_ = v___y_2864_;
v___y_2806_ = v___y_2865_;
v___y_2807_ = v___y_2866_;
v___y_2808_ = v___y_2867_;
v___y_2809_ = v___y_2868_;
v___y_2810_ = v___y_2869_;
v___y_2811_ = v___y_2870_;
v___y_2812_ = v___y_2871_;
v___y_2813_ = v___y_2873_;
v___y_2814_ = v___y_2872_;
v___y_2815_ = v___y_2874_;
v___y_2816_ = v___y_2875_;
v___y_2817_ = v___y_2876_;
v___y_2818_ = v_val_2899_;
v___y_2819_ = v___y_2877_;
v___y_2820_ = v___y_2878_;
v___y_2821_ = v___y_2879_;
v___y_2822_ = v___y_2880_;
v___y_2823_ = v___y_2881_;
v___y_2824_ = v___y_2882_;
v___y_2825_ = v___y_2883_;
v___y_2826_ = v___y_2885_;
v___y_2827_ = v_leFn_x3f_2888_;
v___y_2828_ = v___y_2884_;
v___y_2829_ = v___y_2887_;
v___y_2830_ = v___y_2886_;
v_____do__lift_2831_ = v___x_2903_;
v___y_2832_ = v___y_2889_;
v___y_2833_ = v___y_2890_;
v___y_2834_ = v___y_2891_;
v___y_2835_ = v___y_2892_;
v___y_2836_ = v___y_2893_;
v___y_2837_ = v___y_2894_;
v___y_2838_ = v___y_2895_;
v___y_2839_ = v___y_2896_;
v___y_2840_ = v___y_2897_;
v___y_2841_ = v___y_2898_;
goto v___jp_2801_;
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref_known(v___y_2861_, 1);
lean_dec(v_val_2899_);
lean_dec(v_leFn_x3f_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2862_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2904_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2900_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2900_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_del_object(v___x_2637_);
lean_inc(v___y_2870_);
v___y_2716_ = v___y_2861_;
v___y_2717_ = v___y_2862_;
v___y_2718_ = v___y_2864_;
v___y_2719_ = v___y_2866_;
v___y_2720_ = v___y_2865_;
v___y_2721_ = v___y_2867_;
v___y_2722_ = v___y_2869_;
v___y_2723_ = v___y_2868_;
v___y_2724_ = v___y_2871_;
v___y_2725_ = v___y_2870_;
v___y_2726_ = v___y_2873_;
v___y_2727_ = v___y_2872_;
v___y_2728_ = v___y_2874_;
v___y_2729_ = v___y_2875_;
v___y_2730_ = v___y_2876_;
v___y_2731_ = v___y_2877_;
v___y_2732_ = v___y_2878_;
v___y_2733_ = v___y_2879_;
v___y_2734_ = v___y_2880_;
v___y_2735_ = v___y_2881_;
v___y_2736_ = v___y_2882_;
v___y_2737_ = v___y_2883_;
v___y_2738_ = v___y_2884_;
v___y_2739_ = v_leFn_x3f_2888_;
v___y_2740_ = v___y_2885_;
v___y_2741_ = v___y_2887_;
v_ltFn_x3f_2742_ = v___y_2870_;
v___y_2743_ = v___y_2889_;
v___y_2744_ = v___y_2890_;
v___y_2745_ = v___y_2891_;
v___y_2746_ = v___y_2892_;
v___y_2747_ = v___y_2893_;
v___y_2748_ = v___y_2894_;
v___y_2749_ = v___y_2895_;
v___y_2750_ = v___y_2896_;
v___y_2751_ = v___y_2897_;
v___y_2752_ = v___y_2898_;
goto v___jp_2715_;
}
}
v___jp_2912_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v___y_2915_);
v___x_2954_ = l_Lean_Name_mkStr2(v___y_2915_, v___x_2953_);
lean_inc(v___y_2941_);
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_____do__lift_2942_);
lean_ctor_set(v___x_2955_, 1, v___y_2941_);
v___x_2956_ = l_Lean_mkConst(v___x_2954_, v___x_2955_);
lean_inc_ref(v_type_2547_);
v___x_2957_ = l_Lean_mkAppB(v___x_2956_, v_type_2547_, v___y_2918_);
v___x_2958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2957_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_a_2959_);
v___y_2861_ = v___y_2913_;
v___y_2862_ = v___y_2914_;
v___y_2863_ = v___y_2916_;
v___y_2864_ = v___y_2917_;
v___y_2865_ = v___y_2920_;
v___y_2866_ = v___y_2919_;
v___y_2867_ = v___y_2921_;
v___y_2868_ = v___y_2923_;
v___y_2869_ = v___y_2922_;
v___y_2870_ = v___y_2924_;
v___y_2871_ = v___y_2925_;
v___y_2872_ = v___y_2926_;
v___y_2873_ = v___y_2927_;
v___y_2874_ = v___y_2928_;
v___y_2875_ = v___y_2929_;
v___y_2876_ = v___y_2930_;
v___y_2877_ = v___y_2931_;
v___y_2878_ = v___y_2932_;
v___y_2879_ = v___y_2933_;
v___y_2880_ = v___y_2934_;
v___y_2881_ = v___y_2935_;
v___y_2882_ = v___y_2936_;
v___y_2883_ = v___y_2937_;
v___y_2884_ = v___y_2939_;
v___y_2885_ = v___y_2938_;
v___y_2886_ = v___y_2941_;
v___y_2887_ = v___y_2940_;
v_leFn_x3f_2888_ = v___x_2960_;
v___y_2889_ = v___y_2943_;
v___y_2890_ = v___y_2944_;
v___y_2891_ = v___y_2945_;
v___y_2892_ = v___y_2946_;
v___y_2893_ = v___y_2947_;
v___y_2894_ = v___y_2948_;
v___y_2895_ = v___y_2949_;
v___y_2896_ = v___y_2950_;
v___y_2897_ = v___y_2951_;
v___y_2898_ = v___y_2952_;
goto v___jp_2860_;
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_2961_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2958_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2958_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
v___jp_2969_:
{
lean_object* v___x_3008_; 
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3008_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2630_, v_type_2547_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_3010_, v_val_2630_, v_type_2547_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc_n(v_a_3012_, 2);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
lean_inc(v___y_2986_);
v___x_3014_ = l_Lean_mkConst(v___x_3013_, v___y_2986_);
lean_inc_ref(v_type_2547_);
v___x_3015_ = l_Lean_mkAppB(v___x_3014_, v_type_2547_, v_a_3012_);
v___x_3016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3015_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_2986_);
v___x_3019_ = l_Lean_mkConst(v___x_3018_, v___y_2986_);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15);
lean_inc_ref(v_type_2547_);
v___x_3022_ = l_Lean_mkAppB(v___x_3019_, v_type_2547_, v___x_3021_);
v___x_3023_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3022_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3237_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3237_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3237_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 1)
{
lean_object* v_val_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_del_object(v___x_3026_);
v_val_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v_a_3024_, 1);
v___x_3029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
lean_inc(v___y_2986_);
v___x_3030_ = l_Lean_mkConst(v___x_3029_, v___y_2986_);
lean_inc_ref(v_type_2547_);
v___x_3031_ = l_Lean_mkApp3(v___x_3030_, v_type_2547_, v___x_3021_, v_val_3028_);
v___x_3032_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3031_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_n(v_a_3033_, 2);
lean_dec_ref_known(v___x_3032_, 1);
lean_inc(v_a_3017_);
v___x_3034_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_3017_, v_a_3033_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref_known(v___x_3034_, 1);
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3036_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3035_, v_val_2630_, v_type_2547_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc_n(v_a_3037_, 2);
lean_dec_ref_known(v___x_3036_, 1);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2991_);
v___x_3039_ = l_Lean_mkConst(v___x_3038_, v___y_2991_);
lean_inc_ref_n(v_type_2547_, 3);
v___x_3040_ = l_Lean_mkApp4(v___x_3039_, v_type_2547_, v_type_2547_, v_type_2547_, v_a_3037_);
v___x_3041_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3040_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_3043_, v_val_2630_, v_type_2547_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_n(v_a_3045_, 2);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
v___x_3047_ = l_Lean_mkConst(v___x_3046_, v___y_2986_);
lean_inc_ref(v_type_2547_);
v___x_3048_ = l_Lean_mkAppB(v___x_3047_, v_type_2547_, v_a_3045_);
v___x_3049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3048_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2630_, v_type_2547_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc_n(v_a_3052_, 2);
lean_dec_ref_known(v___x_3051_, 1);
v___x_3053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_3054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___y_2975_);
v___x_3056_ = l_Lean_mkConst(v___x_3053_, v___x_3055_);
v___x_3057_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2547_, 2);
lean_inc_ref(v___x_3056_);
v___x_3058_ = l_Lean_mkApp4(v___x_3056_, v___x_3057_, v_type_2547_, v_type_2547_, v_a_3052_);
v___x_3059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3058_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2630_, v_type_2547_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc_n(v_a_3062_, 2);
lean_dec_ref_known(v___x_3061_, 1);
v___x_3063_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2547_, 2);
v___x_3064_ = l_Lean_mkApp4(v___x_3056_, v___x_3063_, v_type_2547_, v_type_2547_, v_a_3062_);
v___x_3065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3064_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v___x_3067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_3068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3069_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___x_3067_, v___x_3068_);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc_ref(v___y_2993_);
v___x_3070_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_3012_, v___y_2993_, v___x_3069_, v_val_2630_, v_type_2547_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref_known(v___x_3070_, 1);
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3072_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___x_3067_, v___x_3071_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_3074_ = lean_box(0);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2984_, v___y_2993_, v___x_3072_, v___x_3073_, v_val_2630_, v_type_2547_, v___x_3074_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v___x_3075_, 1);
v___x_3076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2990_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3077_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___y_2990_, v___x_3076_);
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc_ref(v___y_2994_);
v___x_3079_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3037_, v___y_2994_, v___x_3077_, v___x_3078_, v_val_2630_, v_type_2547_, v___x_3074_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec_ref_known(v___x_3079_, 1);
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
lean_inc_ref(v___y_2990_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3081_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___y_2990_, v___x_3080_);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3082_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_3045_, v___y_2994_, v___x_3081_, v_val_2630_, v_type_2547_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec_ref_known(v___x_3082_, 1);
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2981_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3084_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___y_2981_, v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_3086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc_ref(v___y_2974_);
v___x_3087_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3052_, v___y_2974_, v___x_3084_, v___x_3085_, v_val_2630_, v_type_2547_, v___x_3086_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3087_, 1);
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2981_);
lean_inc_ref(v___y_2979_);
lean_inc_ref(v___y_2971_);
v___x_3089_ = l_Lean_Name_mkStr4(v___y_2971_, v___y_2979_, v___y_2981_, v___x_3088_);
v___x_3090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc_ref(v___y_2974_);
v___x_3091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3062_, v___y_2974_, v___x_3089_, v___x_3085_, v_val_2630_, v_type_2547_, v___x_3090_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_dec_ref_known(v___x_3091_, 1);
if (lean_obj_tag(v___y_2989_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; 
v_val_3092_ = lean_ctor_get(v___y_2989_, 0);
lean_inc(v_val_3092_);
v___x_3093_ = l_Lean_leCarrierIsSort(v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; uint8_t v___x_3095_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3095_ = lean_unbox(v_a_3094_);
lean_dec(v_a_3094_);
if (v___x_3095_ == 0)
{
lean_inc(v_val_2630_);
v___y_2913_ = v___y_2970_;
v___y_2914_ = v_a_3066_;
v___y_2915_ = v___y_2972_;
v___y_2916_ = v___y_2973_;
v___y_2917_ = v___y_2974_;
v___y_2918_ = v_val_3092_;
v___y_2919_ = v___y_2976_;
v___y_2920_ = v___y_2977_;
v___y_2921_ = v___y_2978_;
v___y_2922_ = v_a_3033_;
v___y_2923_ = v___x_3020_;
v___y_2924_ = v___x_3074_;
v___y_2925_ = v___y_2980_;
v___y_2926_ = v___y_2982_;
v___y_2927_ = v___y_2983_;
v___y_2928_ = v_a_3050_;
v___y_2929_ = v___y_2985_;
v___y_2930_ = v_charInst_x3f_2997_;
v___y_2931_ = v___y_2987_;
v___y_2932_ = v_a_3060_;
v___y_2933_ = v___y_2988_;
v___y_2934_ = v_a_3009_;
v___y_2935_ = v___y_2989_;
v___y_2936_ = v___y_2991_;
v___y_2937_ = v___y_2992_;
v___y_2938_ = v_a_3042_;
v___y_2939_ = v_a_3017_;
v___y_2940_ = v___y_2996_;
v___y_2941_ = v___y_2995_;
v_____do__lift_2942_ = v_val_2630_;
v___y_2943_ = v___y_2998_;
v___y_2944_ = v___y_2999_;
v___y_2945_ = v___y_3000_;
v___y_2946_ = v___y_3001_;
v___y_2947_ = v___y_3002_;
v___y_2948_ = v___y_3003_;
v___y_2949_ = v___y_3004_;
v___y_2950_ = v___y_3005_;
v___y_2951_ = v___y_3006_;
v___y_2952_ = v___y_3007_;
goto v___jp_2912_;
}
else
{
lean_object* v___x_3096_; 
lean_inc(v_val_2630_);
v___x_3096_ = l_Lean_Level_succ___override(v_val_2630_);
v___y_2913_ = v___y_2970_;
v___y_2914_ = v_a_3066_;
v___y_2915_ = v___y_2972_;
v___y_2916_ = v___y_2973_;
v___y_2917_ = v___y_2974_;
v___y_2918_ = v_val_3092_;
v___y_2919_ = v___y_2976_;
v___y_2920_ = v___y_2977_;
v___y_2921_ = v___y_2978_;
v___y_2922_ = v_a_3033_;
v___y_2923_ = v___x_3020_;
v___y_2924_ = v___x_3074_;
v___y_2925_ = v___y_2980_;
v___y_2926_ = v___y_2982_;
v___y_2927_ = v___y_2983_;
v___y_2928_ = v_a_3050_;
v___y_2929_ = v___y_2985_;
v___y_2930_ = v_charInst_x3f_2997_;
v___y_2931_ = v___y_2987_;
v___y_2932_ = v_a_3060_;
v___y_2933_ = v___y_2988_;
v___y_2934_ = v_a_3009_;
v___y_2935_ = v___y_2989_;
v___y_2936_ = v___y_2991_;
v___y_2937_ = v___y_2992_;
v___y_2938_ = v_a_3042_;
v___y_2939_ = v_a_3017_;
v___y_2940_ = v___y_2996_;
v___y_2941_ = v___y_2995_;
v_____do__lift_2942_ = v___x_3096_;
v___y_2943_ = v___y_2998_;
v___y_2944_ = v___y_2999_;
v___y_2945_ = v___y_3000_;
v___y_2946_ = v___y_3001_;
v___y_2947_ = v___y_3002_;
v___y_2948_ = v___y_3003_;
v___y_2949_ = v___y_3004_;
v___y_2950_ = v___y_3005_;
v___y_2951_ = v___y_3006_;
v___y_2952_ = v___y_3007_;
goto v___jp_2912_;
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref_known(v___y_2989_, 1);
lean_dec(v_val_3092_);
lean_dec(v_a_3066_);
lean_dec(v_a_3060_);
lean_dec(v_a_3050_);
lean_dec(v_a_3042_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3097_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3093_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3093_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
v___y_2861_ = v___y_2970_;
v___y_2862_ = v_a_3066_;
v___y_2863_ = v___y_2973_;
v___y_2864_ = v___y_2974_;
v___y_2865_ = v___y_2977_;
v___y_2866_ = v___y_2976_;
v___y_2867_ = v___y_2978_;
v___y_2868_ = v___x_3020_;
v___y_2869_ = v_a_3033_;
v___y_2870_ = v___x_3074_;
v___y_2871_ = v___y_2980_;
v___y_2872_ = v___y_2982_;
v___y_2873_ = v___y_2983_;
v___y_2874_ = v_a_3050_;
v___y_2875_ = v___y_2985_;
v___y_2876_ = v_charInst_x3f_2997_;
v___y_2877_ = v___y_2987_;
v___y_2878_ = v_a_3060_;
v___y_2879_ = v___y_2988_;
v___y_2880_ = v_a_3009_;
v___y_2881_ = v___y_2989_;
v___y_2882_ = v___y_2991_;
v___y_2883_ = v___y_2992_;
v___y_2884_ = v_a_3017_;
v___y_2885_ = v_a_3042_;
v___y_2886_ = v___y_2995_;
v___y_2887_ = v___y_2996_;
v_leFn_x3f_2888_ = v___x_3074_;
v___y_2889_ = v___y_2998_;
v___y_2890_ = v___y_2999_;
v___y_2891_ = v___y_3000_;
v___y_2892_ = v___y_3001_;
v___y_2893_ = v___y_3002_;
v___y_2894_ = v___y_3003_;
v___y_2895_ = v___y_3004_;
v___y_2896_ = v___y_3005_;
v___y_2897_ = v___y_3006_;
v___y_2898_ = v___y_3007_;
goto v___jp_2860_;
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3060_);
lean_dec(v_a_3050_);
lean_dec(v_a_3042_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3105_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3091_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3091_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3050_);
lean_dec(v_a_3042_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3113_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3087_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3087_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3042_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3121_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3082_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3082_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3129_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3079_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3079_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3137_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3075_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3075_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_a_3066_);
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3145_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3070_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3070_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3153_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3065_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3065_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_3060_);
lean_dec_ref(v___x_3056_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3161_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3061_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3061_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v___x_3056_);
lean_dec(v_a_3052_);
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3169_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3059_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3059_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_a_3050_);
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3177_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3051_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3051_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3185_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3049_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3049_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3042_);
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3193_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3044_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3044_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_3037_);
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3201_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3041_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3041_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3209_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3036_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3036_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3033_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3217_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3034_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3034_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3225_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3032_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3032_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
lean_dec(v_a_3024_);
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v___x_3233_ = lean_box(0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3233_);
v___x_3235_ = v___x_3026_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3238_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3023_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3023_);
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
lean_dec(v_a_3012_);
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3246_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3016_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3016_);
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
lean_dec(v_a_3009_);
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3254_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3011_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3011_);
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
lean_dec(v_charInst_x3f_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2978_);
lean_dec(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2970_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3262_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3008_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3008_);
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
v___jp_3270_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc(v___y_3284_);
lean_inc(v___y_3292_);
v___x_3301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v___y_3292_, v___y_3284_, v___y_3272_, v___x_3300_, v_val_2630_, v_type_2547_, v___y_3296_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
lean_inc(v___y_3292_);
v___x_3304_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v___y_3292_, v_a_3302_, v___y_3289_, v___x_3303_, v_val_2630_, v_type_2547_, v___y_3296_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49));
lean_inc_n(v___y_3287_, 2);
v___x_3310_ = l_Lean_mkConst(v___x_3309_, v___y_3287_);
lean_inc_ref(v___y_3277_);
lean_inc_ref_n(v_type_2547_, 3);
v___x_3311_ = l_Lean_mkAppB(v___x_3310_, v_type_2547_, v___y_3277_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52));
v___x_3314_ = l_Lean_mkConst(v___x_3313_, v___y_3287_);
lean_inc_ref(v___x_3311_);
v___x_3315_ = l_Lean_mkAppB(v___x_3314_, v_type_2547_, v___x_3311_);
lean_inc(v___y_3281_);
lean_inc(v_val_2630_);
v___x_3316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2630_, v_type_2547_, v___y_3281_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54));
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3318_, v_val_2630_, v_type_2547_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3321_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2630_, v_type_2547_, v___y_3273_, v___y_3280_, v___y_3286_, v___y_3295_, v___y_3296_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3323_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
lean_inc(v___y_3284_);
lean_inc(v___y_3271_);
lean_inc(v___y_3292_);
lean_inc(v_a_3317_);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3323_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2630_, v_type_2547_, v_a_3317_, v___y_3292_, v___y_3271_, v___y_3284_, v___y_3296_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3323_) == 0)
{
if (lean_obj_tag(v_a_3317_) == 1)
{
lean_object* v_a_3324_; lean_object* v_val_3325_; lean_object* v___x_3326_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v_val_3325_ = lean_ctor_get(v_a_3317_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v_a_3317_, 1);
lean_inc_ref(v_type_2547_);
lean_inc(v_val_2630_);
v___x_3326_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2630_, v_type_2547_, v_val_3325_, v___y_3273_, v___y_3280_, v___y_3286_, v___y_3295_, v___y_3296_, v___y_3298_, v___y_3274_, v___y_3282_, v___y_3279_, v___y_3291_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___y_2970_ = v___y_3271_;
v___y_2971_ = v___x_3306_;
v___y_2972_ = v___y_3275_;
v___y_2973_ = v___y_3276_;
v___y_2974_ = v___y_3277_;
v___y_2975_ = v___y_3278_;
v___y_2976_ = v_a_3322_;
v___y_2977_ = v___y_3299_;
v___y_2978_ = v___y_3281_;
v___y_2979_ = v___x_3307_;
v___y_2980_ = v___y_3283_;
v___y_2981_ = v___x_3308_;
v___y_2982_ = v_a_3305_;
v___y_2983_ = v___y_3284_;
v___y_2984_ = v___y_3285_;
v___y_2985_ = v_a_3324_;
v___y_2986_ = v___y_3287_;
v___y_2987_ = v___y_3288_;
v___y_2988_ = v___y_3290_;
v___y_2989_ = v___y_3292_;
v___y_2990_ = v___x_3312_;
v___y_2991_ = v___y_3293_;
v___y_2992_ = v___y_3294_;
v___y_2993_ = v___x_3315_;
v___y_2994_ = v___x_3311_;
v___y_2995_ = v___y_3297_;
v___y_2996_ = v_a_3320_;
v_charInst_x3f_2997_ = v_a_3327_;
v___y_2998_ = v___y_3273_;
v___y_2999_ = v___y_3280_;
v___y_3000_ = v___y_3286_;
v___y_3001_ = v___y_3295_;
v___y_3002_ = v___y_3296_;
v___y_3003_ = v___y_3298_;
v___y_3004_ = v___y_3274_;
v___y_3005_ = v___y_3282_;
v___y_3006_ = v___y_3279_;
v___y_3007_ = v___y_3291_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_a_3324_);
lean_dec(v_a_3322_);
lean_dec(v_a_3320_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3305_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3328_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3326_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
lean_dec(v_a_3317_);
v_a_3336_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3337_ = lean_box(0);
v___y_2970_ = v___y_3271_;
v___y_2971_ = v___x_3306_;
v___y_2972_ = v___y_3275_;
v___y_2973_ = v___y_3276_;
v___y_2974_ = v___y_3277_;
v___y_2975_ = v___y_3278_;
v___y_2976_ = v_a_3322_;
v___y_2977_ = v___y_3299_;
v___y_2978_ = v___y_3281_;
v___y_2979_ = v___x_3307_;
v___y_2980_ = v___y_3283_;
v___y_2981_ = v___x_3308_;
v___y_2982_ = v_a_3305_;
v___y_2983_ = v___y_3284_;
v___y_2984_ = v___y_3285_;
v___y_2985_ = v_a_3336_;
v___y_2986_ = v___y_3287_;
v___y_2987_ = v___y_3288_;
v___y_2988_ = v___y_3290_;
v___y_2989_ = v___y_3292_;
v___y_2990_ = v___x_3312_;
v___y_2991_ = v___y_3293_;
v___y_2992_ = v___y_3294_;
v___y_2993_ = v___x_3315_;
v___y_2994_ = v___x_3311_;
v___y_2995_ = v___y_3297_;
v___y_2996_ = v_a_3320_;
v_charInst_x3f_2997_ = v___x_3337_;
v___y_2998_ = v___y_3273_;
v___y_2999_ = v___y_3280_;
v___y_3000_ = v___y_3286_;
v___y_3001_ = v___y_3295_;
v___y_3002_ = v___y_3296_;
v___y_3003_ = v___y_3298_;
v___y_3004_ = v___y_3274_;
v___y_3005_ = v___y_3282_;
v___y_3006_ = v___y_3279_;
v___y_3007_ = v___y_3291_;
goto v___jp_2969_;
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3322_);
lean_dec(v_a_3320_);
lean_dec(v_a_3317_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3305_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3338_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3323_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3323_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_a_3320_);
lean_dec(v_a_3317_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3305_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3346_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3321_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3321_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_a_3317_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3305_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3354_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3319_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3319_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___x_3315_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3305_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3362_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3316_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3316_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3370_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3304_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3304_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3281_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3271_);
lean_del_object(v___x_2637_);
lean_dec(v_a_2635_);
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
v_a_3378_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3301_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3301_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec_ref(v_type_2547_);
return v___x_2634_;
}
}
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
lean_dec(v_a_2626_);
lean_dec_ref(v_type_2547_);
v___x_3879_ = lean_box(0);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_3879_);
v___x_3881_ = v___x_2628_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref(v_type_2547_);
v_a_3884_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_2625_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_2625_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
v___jp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2560_);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
v___jp_2563_:
{
if (lean_obj_tag(v___y_2565_) == 0)
{
lean_dec_ref_known(v___y_2565_, 1);
v___y_2560_ = v___y_2564_;
goto v___jp_2559_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v___y_2564_);
v_a_2566_ = lean_ctor_get(v___y_2565_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___y_2565_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___y_2565_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___y_2565_);
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
v___x_2588_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2583_, v___y_2580_, v___y_2585_, v___y_2584_, v___y_2579_, v___y_2586_, v___y_2581_, v___y_2582_, v___y_2575_, v___y_2578_, v___y_2576_, v___y_2577_, v___y_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc_n(v_a_2589_, 2);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2589_, v___y_2585_, v___y_2584_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref_known(v___x_2590_, 1);
v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2589_, v___y_2585_, v___y_2584_);
v___y_2564_ = v___y_2585_;
v___y_2565_ = v___x_2591_;
goto v___jp_2563_;
}
else
{
lean_dec(v_a_2589_);
v___y_2564_ = v___y_2585_;
v___y_2565_ = v___x_2590_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v___y_2585_);
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
v___jp_2600_:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2609_, v___y_2606_, v___y_2611_, v___y_2610_, v___y_2605_, v___y_2612_, v___y_2607_, v___y_2608_, v___y_2601_, v___y_2604_, v___y_2602_, v___y_2603_, v___y_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2615_, v___y_2611_, v___y_2610_);
v___y_2564_ = v___y_2611_;
v___y_2565_ = v___x_2616_;
goto v___jp_2563_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___y_2611_);
v_a_2617_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2614_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2614_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec(v_a_3893_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3906_, v_x_3907_, v_x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3910_, lean_object* v_x_3911_, size_t v_x_3912_, size_t v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3911_, v_x_3912_, v_x_3913_, v_x_3914_, v_x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_){
_start:
{
size_t v_x_804604__boxed_3923_; size_t v_x_804605__boxed_3924_; lean_object* v_res_3925_; 
v_x_804604__boxed_3923_ = lean_unbox_usize(v_x_3919_);
lean_dec(v_x_3919_);
v_x_804605__boxed_3924_ = lean_unbox_usize(v_x_3920_);
lean_dec(v_x_3920_);
v_res_3925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3917_, v_x_3918_, v_x_804604__boxed_3923_, v_x_804605__boxed_3924_, v_x_3921_, v_x_3922_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3926_, lean_object* v_n_3927_, lean_object* v_k_3928_, lean_object* v_v_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3927_, v_k_3928_, v_v_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3931_, size_t v_depth_3932_, lean_object* v_keys_3933_, lean_object* v_vals_3934_, lean_object* v_heq_3935_, lean_object* v_i_3936_, lean_object* v_entries_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3932_, v_keys_3933_, v_vals_3934_, v_i_3936_, v_entries_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3939_, lean_object* v_depth_3940_, lean_object* v_keys_3941_, lean_object* v_vals_3942_, lean_object* v_heq_3943_, lean_object* v_i_3944_, lean_object* v_entries_3945_){
_start:
{
size_t v_depth_boxed_3946_; lean_object* v_res_3947_; 
v_depth_boxed_3946_ = lean_unbox_usize(v_depth_3940_);
lean_dec(v_depth_3940_);
v_res_3947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3939_, v_depth_boxed_3946_, v_keys_3941_, v_vals_3942_, v_heq_3943_, v_i_3944_, v_entries_3945_);
lean_dec_ref(v_vals_3942_);
lean_dec_ref(v_keys_3941_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_, lean_object* v_x_3951_, lean_object* v_x_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3949_, v_x_3950_, v_x_3951_, v_x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3954_, lean_object* v_base_3955_, lean_object* v_natModuleInst_3956_, lean_object* v_declName_3957_, lean_object* v_le_3958_, lean_object* v_mid_3959_, lean_object* v_ord_3960_){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3962_, 0, v_val_3954_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = l_Lean_mkConst(v_declName_3957_, v___x_3962_);
v___x_3964_ = l_Lean_mkApp5(v___x_3963_, v_base_3955_, v_natModuleInst_3956_, v_le_3958_, v_mid_3959_, v_ord_3960_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_4067_, lean_object* v_base_4068_, lean_object* v_natModuleInst_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v___x_4081_; 
lean_inc_ref(v_base_4068_);
v___x_4081_ = l_Lean_Meta_getDecLevel_x3f(v_base_4068_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_5138_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_5138_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_5138_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
if (lean_obj_tag(v_a_4082_) == 1)
{
lean_object* v_val_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_5133_; 
lean_del_object(v___x_4084_);
v_val_4086_ = lean_ctor_get(v_a_4082_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_a_4082_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_4088_ = v_a_4082_;
v_isShared_4089_ = v_isSharedCheck_5133_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_val_4086_);
lean_dec(v_a_4082_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_5133_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v_a_4110_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v_a_4183_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v_leLvl_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v_____do__lift_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v_____do__lift_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v_noNatDivInstQ_x3f_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v_isLinearInstQ_x3f_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___x_4818_; 
v___x_4818_ = l_Lean_leCarrierIsSort(v_a_4078_, v_a_4079_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___y_4821_; lean_object* v___y_4822_; lean_object* v___y_4823_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___y_4827_; lean_object* v___y_4828_; lean_object* v___y_4829_; lean_object* v___y_4830_; lean_object* v_____do__lift_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4863_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v___y_4877_; lean_object* v___y_4878_; lean_object* v___y_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v___y_4906_; lean_object* v___y_4907_; lean_object* v_lawfulOrderLTLvl_4908_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4927_; lean_object* v___y_4928_; lean_object* v___y_4929_; lean_object* v___y_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v___y_4940_; lean_object* v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v___y_4960_; lean_object* v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; lean_object* v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v_____do__lift_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; lean_object* v_____do__lift_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; uint8_t v___x_5123_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
lean_inc(v_a_4819_);
lean_dec_ref_known(v___x_4818_, 1);
v___x_5123_ = lean_unbox(v_a_4819_);
lean_dec(v_a_4819_);
if (v___x_5123_ == 0)
{
lean_inc(v_val_4086_);
v_____do__lift_5088_ = v_val_4086_;
v___y_5089_ = v_a_4070_;
v___y_5090_ = v_a_4071_;
v___y_5091_ = v_a_4072_;
v___y_5092_ = v_a_4073_;
v___y_5093_ = v_a_4074_;
v___y_5094_ = v_a_4075_;
v___y_5095_ = v_a_4076_;
v___y_5096_ = v_a_4077_;
v___y_5097_ = v_a_4078_;
v___y_5098_ = v_a_4079_;
goto v___jp_5087_;
}
else
{
lean_object* v___x_5124_; 
lean_inc(v_val_4086_);
v___x_5124_ = l_Lean_Level_succ___override(v_val_4086_);
v_____do__lift_5088_ = v___x_5124_;
v___y_5089_ = v_a_4070_;
v___y_5090_ = v_a_4071_;
v___y_5091_ = v_a_4072_;
v___y_5092_ = v_a_4073_;
v___y_5093_ = v_a_4074_;
v___y_5094_ = v_a_4075_;
v___y_5095_ = v_a_4076_;
v___y_5096_ = v_a_4077_;
v___y_5097_ = v_a_4078_;
v___y_5098_ = v_a_4079_;
goto v___jp_5087_;
}
v___jp_4820_:
{
lean_object* v___x_4842_; 
lean_inc_ref(v_base_4068_);
v___x_4842_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_____do__lift_4831_, v_base_4068_, v___y_4822_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
if (lean_obj_tag(v_a_4843_) == 0)
{
lean_dec_ref(v___y_4829_);
lean_dec_ref(v___y_4821_);
v___y_4743_ = v___y_4823_;
v___y_4744_ = v___y_4824_;
v___y_4745_ = v___y_4825_;
v___y_4746_ = v___y_4826_;
v___y_4747_ = v___y_4828_;
v___y_4748_ = v___y_4827_;
v___y_4749_ = v___y_4830_;
v_isLinearInstQ_x3f_4750_ = v_a_4843_;
v___y_4751_ = v___y_4832_;
v___y_4752_ = v___y_4833_;
v___y_4753_ = v___y_4834_;
v___y_4754_ = v___y_4835_;
v___y_4755_ = v___y_4836_;
v___y_4756_ = v___y_4837_;
v___y_4757_ = v___y_4838_;
v___y_4758_ = v___y_4839_;
v___y_4759_ = v___y_4840_;
v___y_4760_ = v___y_4841_;
goto v___jp_4742_;
}
else
{
lean_object* v_val_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4853_; 
v_val_4844_ = lean_ctor_get(v_a_4843_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_a_4843_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4846_ = v_a_4843_;
v_isShared_4847_ = v_isSharedCheck_4853_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_val_4844_);
lean_dec(v_a_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4853_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4851_; 
v___x_4848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19));
lean_inc_ref(v_natModuleInst_4069_);
lean_inc_ref(v_base_4068_);
lean_inc(v_val_4086_);
v___x_4849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4086_, v_base_4068_, v_natModuleInst_4069_, v___x_4848_, v___y_4821_, v_val_4844_, v___y_4829_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v___x_4849_);
v___x_4851_ = v___x_4846_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
v___y_4743_ = v___y_4823_;
v___y_4744_ = v___y_4824_;
v___y_4745_ = v___y_4825_;
v___y_4746_ = v___y_4826_;
v___y_4747_ = v___y_4828_;
v___y_4748_ = v___y_4827_;
v___y_4749_ = v___y_4830_;
v_isLinearInstQ_x3f_4750_ = v___x_4851_;
v___y_4751_ = v___y_4832_;
v___y_4752_ = v___y_4833_;
v___y_4753_ = v___y_4834_;
v___y_4754_ = v___y_4835_;
v___y_4755_ = v___y_4836_;
v___y_4756_ = v___y_4837_;
v___y_4757_ = v___y_4838_;
v___y_4758_ = v___y_4839_;
v___y_4759_ = v___y_4840_;
v___y_4760_ = v___y_4841_;
goto v___jp_4742_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4821_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4854_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4842_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4842_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
v___jp_4862_:
{
if (lean_obj_tag(v___y_4863_) == 0)
{
lean_object* v___x_4882_; 
lean_dec(v___y_4865_);
v___x_4882_ = lean_box(0);
v___y_4743_ = v___y_4875_;
v___y_4744_ = v___y_4881_;
v___y_4745_ = v___y_4877_;
v___y_4746_ = v___y_4872_;
v___y_4747_ = v___y_4873_;
v___y_4748_ = v___y_4878_;
v___y_4749_ = v___y_4880_;
v_isLinearInstQ_x3f_4750_ = v___x_4882_;
v___y_4751_ = v___y_4874_;
v___y_4752_ = v___y_4868_;
v___y_4753_ = v___y_4870_;
v___y_4754_ = v___y_4864_;
v___y_4755_ = v___y_4871_;
v___y_4756_ = v___y_4869_;
v___y_4757_ = v___y_4867_;
v___y_4758_ = v___y_4876_;
v___y_4759_ = v___y_4879_;
v___y_4760_ = v___y_4866_;
goto v___jp_4742_;
}
else
{
lean_object* v_val_4883_; lean_object* v_snd_4884_; lean_object* v_fst_4885_; lean_object* v_snd_4886_; lean_object* v___x_4887_; 
v_val_4883_ = lean_ctor_get(v___y_4863_, 0);
lean_inc(v_val_4883_);
lean_dec_ref_known(v___y_4863_, 1);
v_snd_4884_ = lean_ctor_get(v_val_4883_, 1);
lean_inc(v_snd_4884_);
v_fst_4885_ = lean_ctor_get(v_val_4883_, 0);
lean_inc(v_fst_4885_);
lean_dec(v_val_4883_);
v_snd_4886_ = lean_ctor_get(v_snd_4884_, 1);
lean_inc(v_snd_4886_);
lean_dec(v_snd_4884_);
v___x_4887_ = l_Lean_leCarrierIsSort(v___y_4879_, v___y_4866_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; uint8_t v___x_4889_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v___x_4889_ = lean_unbox(v_a_4888_);
lean_dec(v_a_4888_);
if (v___x_4889_ == 0)
{
lean_inc(v_val_4086_);
v___y_4821_ = v_fst_4885_;
v___y_4822_ = v___y_4865_;
v___y_4823_ = v___y_4875_;
v___y_4824_ = v___y_4881_;
v___y_4825_ = v___y_4877_;
v___y_4826_ = v___y_4872_;
v___y_4827_ = v___y_4878_;
v___y_4828_ = v___y_4873_;
v___y_4829_ = v_snd_4886_;
v___y_4830_ = v___y_4880_;
v_____do__lift_4831_ = v_val_4086_;
v___y_4832_ = v___y_4874_;
v___y_4833_ = v___y_4868_;
v___y_4834_ = v___y_4870_;
v___y_4835_ = v___y_4864_;
v___y_4836_ = v___y_4871_;
v___y_4837_ = v___y_4869_;
v___y_4838_ = v___y_4867_;
v___y_4839_ = v___y_4876_;
v___y_4840_ = v___y_4879_;
v___y_4841_ = v___y_4866_;
goto v___jp_4820_;
}
else
{
lean_object* v___x_4890_; 
lean_inc(v_val_4086_);
v___x_4890_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_4821_ = v_fst_4885_;
v___y_4822_ = v___y_4865_;
v___y_4823_ = v___y_4875_;
v___y_4824_ = v___y_4881_;
v___y_4825_ = v___y_4877_;
v___y_4826_ = v___y_4872_;
v___y_4827_ = v___y_4878_;
v___y_4828_ = v___y_4873_;
v___y_4829_ = v_snd_4886_;
v___y_4830_ = v___y_4880_;
v_____do__lift_4831_ = v___x_4890_;
v___y_4832_ = v___y_4874_;
v___y_4833_ = v___y_4868_;
v___y_4834_ = v___y_4870_;
v___y_4835_ = v___y_4864_;
v___y_4836_ = v___y_4871_;
v___y_4837_ = v___y_4869_;
v___y_4838_ = v___y_4867_;
v___y_4839_ = v___y_4876_;
v___y_4840_ = v___y_4879_;
v___y_4841_ = v___y_4866_;
goto v___jp_4820_;
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec(v_snd_4886_);
lean_dec(v_fst_4885_);
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec(v___y_4878_);
lean_dec(v___y_4875_);
lean_dec(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec(v___y_4865_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4891_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4887_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4887_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
v___jp_4899_:
{
if (lean_obj_tag(v___y_4905_) == 0)
{
lean_dec(v_lawfulOrderLTLvl_4908_);
v___y_4863_ = v___y_4900_;
v___y_4864_ = v___y_4912_;
v___y_4865_ = v___y_4901_;
v___y_4866_ = v___y_4918_;
v___y_4867_ = v___y_4915_;
v___y_4868_ = v___y_4910_;
v___y_4869_ = v___y_4914_;
v___y_4870_ = v___y_4911_;
v___y_4871_ = v___y_4913_;
v___y_4872_ = v___y_4904_;
v___y_4873_ = v___y_4906_;
v___y_4874_ = v___y_4909_;
v___y_4875_ = v___y_4902_;
v___y_4876_ = v___y_4916_;
v___y_4877_ = v___y_4903_;
v___y_4878_ = v___y_4905_;
v___y_4879_ = v___y_4917_;
v___y_4880_ = v___y_4907_;
v___y_4881_ = v___y_4905_;
goto v___jp_4862_;
}
else
{
lean_object* v_val_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v_val_4919_ = lean_ctor_get(v___y_4905_, 0);
v___x_4920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23));
v___x_4921_ = lean_box(0);
v___x_4922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4922_, 0, v_lawfulOrderLTLvl_4908_);
lean_ctor_set(v___x_4922_, 1, v___x_4921_);
v___x_4923_ = l_Lean_mkConst(v___x_4920_, v___x_4922_);
lean_inc(v_val_4919_);
lean_inc_ref(v_type_4067_);
v___x_4924_ = l_Lean_mkAppB(v___x_4923_, v_type_4067_, v_val_4919_);
v___x_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
v___y_4863_ = v___y_4900_;
v___y_4864_ = v___y_4912_;
v___y_4865_ = v___y_4901_;
v___y_4866_ = v___y_4918_;
v___y_4867_ = v___y_4915_;
v___y_4868_ = v___y_4910_;
v___y_4869_ = v___y_4914_;
v___y_4870_ = v___y_4911_;
v___y_4871_ = v___y_4913_;
v___y_4872_ = v___y_4904_;
v___y_4873_ = v___y_4906_;
v___y_4874_ = v___y_4909_;
v___y_4875_ = v___y_4902_;
v___y_4876_ = v___y_4916_;
v___y_4877_ = v___y_4903_;
v___y_4878_ = v___y_4905_;
v___y_4879_ = v___y_4917_;
v___y_4880_ = v___y_4907_;
v___y_4881_ = v___x_4925_;
goto v___jp_4862_;
}
}
v___jp_4926_:
{
lean_object* v___x_4945_; 
v___x_4945_ = l_Lean_leCarrierIsSort(v___y_4941_, v___y_4936_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; uint8_t v___x_4947_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___x_4945_, 1);
v___x_4947_ = lean_unbox(v_a_4946_);
lean_dec(v_a_4946_);
if (v___x_4947_ == 0)
{
lean_inc(v_val_4086_);
v___y_4900_ = v___y_4928_;
v___y_4901_ = v___y_4930_;
v___y_4902_ = v___y_4935_;
v___y_4903_ = v___y_4937_;
v___y_4904_ = v___y_4931_;
v___y_4905_ = v___y_4940_;
v___y_4906_ = v___y_4944_;
v___y_4907_ = v___y_4943_;
v_lawfulOrderLTLvl_4908_ = v_val_4086_;
v___y_4909_ = v___y_4929_;
v___y_4910_ = v___y_4942_;
v___y_4911_ = v___y_4927_;
v___y_4912_ = v___y_4939_;
v___y_4913_ = v___y_4932_;
v___y_4914_ = v___y_4933_;
v___y_4915_ = v___y_4938_;
v___y_4916_ = v___y_4934_;
v___y_4917_ = v___y_4941_;
v___y_4918_ = v___y_4936_;
goto v___jp_4899_;
}
else
{
lean_object* v___x_4948_; 
lean_inc(v_val_4086_);
v___x_4948_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_4900_ = v___y_4928_;
v___y_4901_ = v___y_4930_;
v___y_4902_ = v___y_4935_;
v___y_4903_ = v___y_4937_;
v___y_4904_ = v___y_4931_;
v___y_4905_ = v___y_4940_;
v___y_4906_ = v___y_4944_;
v___y_4907_ = v___y_4943_;
v_lawfulOrderLTLvl_4908_ = v___x_4948_;
v___y_4909_ = v___y_4929_;
v___y_4910_ = v___y_4942_;
v___y_4911_ = v___y_4927_;
v___y_4912_ = v___y_4939_;
v___y_4913_ = v___y_4932_;
v___y_4914_ = v___y_4933_;
v___y_4915_ = v___y_4938_;
v___y_4916_ = v___y_4934_;
v___y_4917_ = v___y_4941_;
v___y_4918_ = v___y_4936_;
goto v___jp_4899_;
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v___y_4944_);
lean_dec(v___y_4943_);
lean_dec(v___y_4940_);
lean_dec(v___y_4935_);
lean_dec(v___y_4931_);
lean_dec(v___y_4930_);
lean_dec(v___y_4928_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4949_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4945_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4945_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
v___jp_4957_:
{
lean_object* v___x_4972_; 
v___x_4972_ = lean_box(0);
lean_inc(v___y_4971_);
v___y_4927_ = v___y_4958_;
v___y_4928_ = v___y_4971_;
v___y_4929_ = v___y_4959_;
v___y_4930_ = v___y_4960_;
v___y_4931_ = v___x_4972_;
v___y_4932_ = v___y_4961_;
v___y_4933_ = v___y_4962_;
v___y_4934_ = v___y_4963_;
v___y_4935_ = v___y_4964_;
v___y_4936_ = v___y_4965_;
v___y_4937_ = v___y_4966_;
v___y_4938_ = v___y_4967_;
v___y_4939_ = v___y_4968_;
v___y_4940_ = v___x_4972_;
v___y_4941_ = v___y_4969_;
v___y_4942_ = v___y_4970_;
v___y_4943_ = v___x_4972_;
v___y_4944_ = v___x_4972_;
goto v___jp_4926_;
}
v___jp_4973_:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_box(0);
v___y_4958_ = v___y_4979_;
v___y_4959_ = v___y_4977_;
v___y_4960_ = v___y_4974_;
v___y_4961_ = v___y_4981_;
v___y_4962_ = v___y_4982_;
v___y_4963_ = v___y_4984_;
v___y_4964_ = v___y_4975_;
v___y_4965_ = v___y_4986_;
v___y_4966_ = v___y_4976_;
v___y_4967_ = v___y_4983_;
v___y_4968_ = v___y_4980_;
v___y_4969_ = v___y_4985_;
v___y_4970_ = v___y_4978_;
v___y_4971_ = v___x_4987_;
goto v___jp_4957_;
}
v___jp_4988_:
{
if (lean_obj_tag(v___y_4991_) == 0)
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_box(0);
v___y_4958_ = v___y_4995_;
v___y_4959_ = v___y_4993_;
v___y_4960_ = v___y_4989_;
v___y_4961_ = v___y_4997_;
v___y_4962_ = v___y_4998_;
v___y_4963_ = v___y_5000_;
v___y_4964_ = v___y_4990_;
v___y_4965_ = v___y_5002_;
v___y_4966_ = v___y_4992_;
v___y_4967_ = v___y_4999_;
v___y_4968_ = v___y_4996_;
v___y_4969_ = v___y_5001_;
v___y_4970_ = v___y_4994_;
v___y_4971_ = v___x_5003_;
goto v___jp_4957_;
}
else
{
lean_dec_ref_known(v___y_4991_, 1);
v___y_4974_ = v___y_4989_;
v___y_4975_ = v___y_4990_;
v___y_4976_ = v___y_4992_;
v___y_4977_ = v___y_4993_;
v___y_4978_ = v___y_4994_;
v___y_4979_ = v___y_4995_;
v___y_4980_ = v___y_4996_;
v___y_4981_ = v___y_4997_;
v___y_4982_ = v___y_4998_;
v___y_4983_ = v___y_4999_;
v___y_4984_ = v___y_5000_;
v___y_4985_ = v___y_5001_;
v___y_4986_ = v___y_5002_;
goto v___jp_4973_;
}
}
v___jp_5004_:
{
lean_object* v___x_5019_; 
lean_inc(v___y_5005_);
lean_inc_ref(v_base_4068_);
v___x_5019_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_____do__lift_5008_, v_base_4068_, v___y_5005_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5019_) == 0)
{
if (lean_obj_tag(v___y_5005_) == 1)
{
lean_object* v_a_5020_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
lean_dec_ref_known(v___x_5019_, 1);
if (lean_obj_tag(v_a_5020_) == 1)
{
lean_object* v_val_5021_; lean_object* v_val_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5076_; 
v_val_5021_ = lean_ctor_get(v___y_5005_, 0);
v_val_5022_ = lean_ctor_get(v_a_5020_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_a_5020_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5024_ = v_a_5020_;
v_isShared_5025_ = v_isSharedCheck_5076_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_val_5022_);
lean_dec(v_a_5020_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5076_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_base_4068_);
lean_inc(v_val_4086_);
v___x_5027_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_5026_, v_val_4086_, v_base_4068_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v___x_5027_, 1);
v___x_5029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
v___x_5030_ = lean_box(0);
lean_inc(v_val_4086_);
v___x_5031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5031_, 0, v_val_4086_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
v___x_5032_ = l_Lean_mkConst(v___x_5029_, v___x_5031_);
lean_inc(v_val_5022_);
lean_inc(v_val_5021_);
lean_inc_ref(v_base_4068_);
v___x_5033_ = l_Lean_mkApp4(v___x_5032_, v_base_4068_, v_a_5028_, v_val_5021_, v_val_5022_);
v___x_5034_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5033_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
if (lean_obj_tag(v_a_5035_) == 0)
{
lean_del_object(v___x_5024_);
lean_dec(v_val_5022_);
v___y_4974_ = v___y_5005_;
v___y_4975_ = v___y_5006_;
v___y_4976_ = v___y_5007_;
v___y_4977_ = v___y_5009_;
v___y_4978_ = v___y_5010_;
v___y_4979_ = v___y_5011_;
v___y_4980_ = v___y_5012_;
v___y_4981_ = v___y_5013_;
v___y_4982_ = v___y_5014_;
v___y_4983_ = v___y_5015_;
v___y_4984_ = v___y_5016_;
v___y_4985_ = v___y_5017_;
v___y_4986_ = v___y_5018_;
goto v___jp_4973_;
}
else
{
lean_object* v_val_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5059_; 
v_val_5036_ = lean_ctor_get(v_a_5035_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v_a_5035_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5038_ = v_a_5035_;
v_isShared_5039_ = v_isSharedCheck_5059_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_val_5036_);
lean_dec(v_a_5035_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5059_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5043_; 
lean_inc(v_val_5036_);
lean_inc(v_val_5022_);
v___x_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5040_, 0, v_val_5022_);
lean_ctor_set(v___x_5040_, 1, v_val_5036_);
lean_inc(v_val_5021_);
v___x_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5041_, 0, v_val_5021_);
lean_ctor_set(v___x_5041_, 1, v___x_5040_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 0, v___x_5041_);
v___x_5043_ = v___x_5038_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25));
lean_inc(v_val_5036_);
lean_inc(v_val_5022_);
lean_inc(v_val_5021_);
lean_inc_ref(v_natModuleInst_4069_);
lean_inc_ref(v_base_4068_);
lean_inc(v_val_4086_);
v___x_5045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4086_, v_base_4068_, v_natModuleInst_4069_, v___x_5044_, v_val_5021_, v_val_5022_, v_val_5036_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 0, v___x_5045_);
v___x_5047_ = v___x_5024_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27));
lean_inc_n(v_val_5036_, 2);
lean_inc_n(v_val_5022_, 2);
lean_inc_n(v_val_5021_, 3);
lean_inc_ref_n(v_natModuleInst_4069_, 3);
lean_inc_ref_n(v_base_4068_, 3);
lean_inc_n(v_val_4086_, 3);
v___x_5049_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4086_, v_base_4068_, v_natModuleInst_4069_, v___x_5048_, v_val_5021_, v_val_5022_, v_val_5036_);
v___x_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5049_);
v___x_5051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29));
v___x_5052_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4086_, v_base_4068_, v_natModuleInst_4069_, v___x_5051_, v_val_5021_, v_val_5022_, v_val_5036_);
v___x_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
v___x_5054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31));
v___x_5055_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4086_, v_base_4068_, v_natModuleInst_4069_, v___x_5054_, v_val_5021_, v_val_5022_, v_val_5036_);
v___x_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
v___y_4927_ = v___y_5011_;
v___y_4928_ = v___x_5043_;
v___y_4929_ = v___y_5009_;
v___y_4930_ = v___y_5005_;
v___y_4931_ = v___x_5050_;
v___y_4932_ = v___y_5013_;
v___y_4933_ = v___y_5014_;
v___y_4934_ = v___y_5016_;
v___y_4935_ = v___y_5006_;
v___y_4936_ = v___y_5018_;
v___y_4937_ = v___y_5007_;
v___y_4938_ = v___y_5015_;
v___y_4939_ = v___y_5012_;
v___y_4940_ = v___x_5047_;
v___y_4941_ = v___y_5017_;
v___y_4942_ = v___y_5010_;
v___y_4943_ = v___x_5053_;
v___y_4944_ = v___x_5056_;
goto v___jp_4926_;
}
}
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_del_object(v___x_5024_);
lean_dec(v_val_5022_);
lean_dec_ref_known(v___y_5005_, 1);
lean_dec(v___y_5006_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5060_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5034_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5034_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_del_object(v___x_5024_);
lean_dec(v_val_5022_);
lean_dec_ref_known(v___y_5005_, 1);
lean_dec(v___y_5006_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5068_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5027_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5027_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
else
{
v___y_4989_ = v___y_5005_;
v___y_4990_ = v___y_5006_;
v___y_4991_ = v_a_5020_;
v___y_4992_ = v___y_5007_;
v___y_4993_ = v___y_5009_;
v___y_4994_ = v___y_5010_;
v___y_4995_ = v___y_5011_;
v___y_4996_ = v___y_5012_;
v___y_4997_ = v___y_5013_;
v___y_4998_ = v___y_5014_;
v___y_4999_ = v___y_5015_;
v___y_5000_ = v___y_5016_;
v___y_5001_ = v___y_5017_;
v___y_5002_ = v___y_5018_;
goto v___jp_4988_;
}
}
else
{
if (lean_obj_tag(v___y_5005_) == 0)
{
lean_object* v___x_5077_; 
lean_dec_ref_known(v___x_5019_, 1);
v___x_5077_ = lean_box(0);
v___y_4958_ = v___y_5011_;
v___y_4959_ = v___y_5009_;
v___y_4960_ = v___y_5005_;
v___y_4961_ = v___y_5013_;
v___y_4962_ = v___y_5014_;
v___y_4963_ = v___y_5016_;
v___y_4964_ = v___y_5006_;
v___y_4965_ = v___y_5018_;
v___y_4966_ = v___y_5007_;
v___y_4967_ = v___y_5015_;
v___y_4968_ = v___y_5012_;
v___y_4969_ = v___y_5017_;
v___y_4970_ = v___y_5010_;
v___y_4971_ = v___x_5077_;
goto v___jp_4957_;
}
else
{
lean_object* v_a_5078_; 
v_a_5078_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5019_, 1);
v___y_4989_ = v___y_5005_;
v___y_4990_ = v___y_5006_;
v___y_4991_ = v_a_5078_;
v___y_4992_ = v___y_5007_;
v___y_4993_ = v___y_5009_;
v___y_4994_ = v___y_5010_;
v___y_4995_ = v___y_5011_;
v___y_4996_ = v___y_5012_;
v___y_4997_ = v___y_5013_;
v___y_4998_ = v___y_5014_;
v___y_4999_ = v___y_5015_;
v___y_5000_ = v___y_5016_;
v___y_5001_ = v___y_5017_;
v___y_5002_ = v___y_5018_;
goto v___jp_4988_;
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
lean_dec(v___y_5006_);
lean_dec(v___y_5005_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5079_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5019_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5019_);
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
v___jp_5087_:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
v___x_5100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_base_4068_);
v___x_5101_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5100_, v_____do__lift_5088_, v_base_4068_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5103_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5101_, 1);
v___x_5103_ = l_Lean_leCarrierIsSort(v___y_5097_, v___y_5098_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; uint8_t v___x_5105_; 
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5103_, 1);
v___x_5105_ = lean_unbox(v_a_5104_);
lean_dec(v_a_5104_);
if (v___x_5105_ == 0)
{
lean_inc(v_val_4086_);
v___y_5005_ = v_a_5102_;
v___y_5006_ = v___x_5100_;
v___y_5007_ = v___x_5099_;
v_____do__lift_5008_ = v_val_4086_;
v___y_5009_ = v___y_5089_;
v___y_5010_ = v___y_5090_;
v___y_5011_ = v___y_5091_;
v___y_5012_ = v___y_5092_;
v___y_5013_ = v___y_5093_;
v___y_5014_ = v___y_5094_;
v___y_5015_ = v___y_5095_;
v___y_5016_ = v___y_5096_;
v___y_5017_ = v___y_5097_;
v___y_5018_ = v___y_5098_;
goto v___jp_5004_;
}
else
{
lean_object* v___x_5106_; 
lean_inc(v_val_4086_);
v___x_5106_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_5005_ = v_a_5102_;
v___y_5006_ = v___x_5100_;
v___y_5007_ = v___x_5099_;
v_____do__lift_5008_ = v___x_5106_;
v___y_5009_ = v___y_5089_;
v___y_5010_ = v___y_5090_;
v___y_5011_ = v___y_5091_;
v___y_5012_ = v___y_5092_;
v___y_5013_ = v___y_5093_;
v___y_5014_ = v___y_5094_;
v___y_5015_ = v___y_5095_;
v___y_5016_ = v___y_5096_;
v___y_5017_ = v___y_5097_;
v___y_5018_ = v___y_5098_;
goto v___jp_5004_;
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_a_5102_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5107_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5103_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5103_);
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
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5115_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5101_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5101_);
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
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5125_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_4818_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_4818_);
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
v___jp_4090_:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4093_, v___y_4107_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v_structs_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v_structs_4113_ = lean_ctor_get(v_a_4112_, 0);
lean_inc_ref(v_structs_4113_);
lean_dec(v_a_4112_);
v___x_4114_ = lean_array_get_size(v_structs_4113_);
lean_dec_ref(v_structs_4113_);
v___x_4115_ = lean_box(0);
lean_inc_ref(v___y_4099_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set(v___x_4088_, 0, v___y_4099_);
v___x_4117_ = v___x_4088_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___y_4099_);
v___x_4117_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; size_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___f_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_inc_ref(v___y_4098_);
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___y_4098_);
v___x_4119_ = lean_unsigned_to_nat(32u);
v___x_4120_ = lean_mk_empty_array_with_capacity(v___x_4119_);
v___x_4121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0);
v___x_4122_ = ((size_t)5ULL);
lean_inc(v___y_4097_);
v___x_4123_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4120_);
lean_ctor_set(v___x_4123_, 2, v___y_4097_);
lean_ctor_set(v___x_4123_, 3, v___y_4097_);
lean_ctor_set_usize(v___x_4123_, 4, v___x_4122_);
v___x_4124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2);
v___x_4125_ = 0;
v___x_4126_ = lean_box(0);
lean_inc_ref_n(v___x_4123_, 7);
v___x_4127_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_4127_, 0, v___x_4114_);
lean_ctor_set(v___x_4127_, 1, v___x_4115_);
lean_ctor_set(v___x_4127_, 2, v_type_4067_);
lean_ctor_set(v___x_4127_, 3, v_val_4086_);
lean_ctor_set(v___x_4127_, 4, v___y_4106_);
lean_ctor_set(v___x_4127_, 5, v___y_4108_);
lean_ctor_set(v___x_4127_, 6, v___y_4101_);
lean_ctor_set(v___x_4127_, 7, v___y_4100_);
lean_ctor_set(v___x_4127_, 8, v___y_4109_);
lean_ctor_set(v___x_4127_, 9, v___y_4102_);
lean_ctor_set(v___x_4127_, 10, v___y_4104_);
lean_ctor_set(v___x_4127_, 11, v___y_4094_);
lean_ctor_set(v___x_4127_, 12, v___x_4115_);
lean_ctor_set(v___x_4127_, 13, v___x_4115_);
lean_ctor_set(v___x_4127_, 14, v___x_4115_);
lean_ctor_set(v___x_4127_, 15, v___x_4115_);
lean_ctor_set(v___x_4127_, 16, v___x_4115_);
lean_ctor_set(v___x_4127_, 17, v___y_4092_);
lean_ctor_set(v___x_4127_, 18, v___y_4096_);
lean_ctor_set(v___x_4127_, 19, v___x_4115_);
lean_ctor_set(v___x_4127_, 20, v___y_4105_);
lean_ctor_set(v___x_4127_, 21, v_a_4110_);
lean_ctor_set(v___x_4127_, 22, v___y_4095_);
lean_ctor_set(v___x_4127_, 23, v___y_4099_);
lean_ctor_set(v___x_4127_, 24, v___y_4098_);
lean_ctor_set(v___x_4127_, 25, v___x_4117_);
lean_ctor_set(v___x_4127_, 26, v___x_4118_);
lean_ctor_set(v___x_4127_, 27, v___x_4115_);
lean_ctor_set(v___x_4127_, 28, v___y_4091_);
lean_ctor_set(v___x_4127_, 29, v___y_4103_);
lean_ctor_set(v___x_4127_, 30, v___x_4123_);
lean_ctor_set(v___x_4127_, 31, v___x_4124_);
lean_ctor_set(v___x_4127_, 32, v___x_4123_);
lean_ctor_set(v___x_4127_, 33, v___x_4123_);
lean_ctor_set(v___x_4127_, 34, v___x_4123_);
lean_ctor_set(v___x_4127_, 35, v___x_4123_);
lean_ctor_set(v___x_4127_, 36, v___x_4115_);
lean_ctor_set(v___x_4127_, 37, v___x_4124_);
lean_ctor_set(v___x_4127_, 38, v___x_4123_);
lean_ctor_set(v___x_4127_, 39, v___x_4126_);
lean_ctor_set(v___x_4127_, 40, v___x_4123_);
lean_ctor_set(v___x_4127_, 41, v___x_4123_);
lean_ctor_set_uint8(v___x_4127_, sizeof(void*)*42, v___x_4125_);
v___f_4128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_4128_, 0, v___x_4127_);
v___x_4129_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4130_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4129_, v___f_4128_, v___y_4093_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4138_; 
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v___x_4130_, 0);
lean_dec(v_unused_4139_);
v___x_4132_ = v___x_4130_;
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
else
{
lean_dec(v___x_4130_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4114_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v___x_4134_);
v___x_4136_ = v___x_4132_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_a_4140_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4130_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4130_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec(v_a_4110_);
lean_dec(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4149_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4111_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4111_);
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
v___jp_4157_:
{
if (lean_obj_tag(v___y_4177_) == 0)
{
lean_dec(v___y_4167_);
v___y_4091_ = v___y_4173_;
v___y_4092_ = v___y_4172_;
v___y_4093_ = v___y_4174_;
v___y_4094_ = v___y_4158_;
v___y_4095_ = v___y_4159_;
v___y_4096_ = v___y_4161_;
v___y_4097_ = v___y_4160_;
v___y_4098_ = v___y_4175_;
v___y_4099_ = v___y_4162_;
v___y_4100_ = v___y_4176_;
v___y_4101_ = v___y_4177_;
v___y_4102_ = v___y_4163_;
v___y_4103_ = v___y_4165_;
v___y_4104_ = v___y_4168_;
v___y_4105_ = v_a_4183_;
v___y_4106_ = v___y_4179_;
v___y_4107_ = v___y_4170_;
v___y_4108_ = v___y_4171_;
v___y_4109_ = v___y_4182_;
v_a_4110_ = v___y_4177_;
goto v___jp_4090_;
}
else
{
lean_object* v_val_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_val_4184_ = lean_ctor_get(v___y_4177_, 0);
v___x_4185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0));
lean_inc(v___y_4169_);
v___x_4186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___y_4167_);
lean_ctor_set(v___x_4186_, 1, v___y_4169_);
v___x_4187_ = l_Lean_mkConst(v___x_4185_, v___x_4186_);
lean_inc(v_val_4184_);
lean_inc_ref(v_type_4067_);
v___x_4188_ = l_Lean_mkAppB(v___x_4187_, v_type_4067_, v_val_4184_);
v___x_4189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4188_, v___y_4178_, v___y_4166_, v___y_4181_, v___y_4164_, v___y_4170_, v___y_4180_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4191_, 0, v_a_4190_);
v___y_4091_ = v___y_4173_;
v___y_4092_ = v___y_4172_;
v___y_4093_ = v___y_4174_;
v___y_4094_ = v___y_4158_;
v___y_4095_ = v___y_4159_;
v___y_4096_ = v___y_4161_;
v___y_4097_ = v___y_4160_;
v___y_4098_ = v___y_4175_;
v___y_4099_ = v___y_4162_;
v___y_4100_ = v___y_4176_;
v___y_4101_ = v___y_4177_;
v___y_4102_ = v___y_4163_;
v___y_4103_ = v___y_4165_;
v___y_4104_ = v___y_4168_;
v___y_4105_ = v_a_4183_;
v___y_4106_ = v___y_4179_;
v___y_4107_ = v___y_4170_;
v___y_4108_ = v___y_4171_;
v___y_4109_ = v___y_4182_;
v_a_4110_ = v___x_4191_;
goto v___jp_4090_;
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref_known(v___y_4177_, 1);
lean_dec(v_a_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4192_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4189_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4189_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
v___jp_4200_:
{
if (lean_obj_tag(v___y_4217_) == 0)
{
v___y_4158_ = v___y_4203_;
v___y_4159_ = v___y_4204_;
v___y_4160_ = v___y_4205_;
v___y_4161_ = v___y_4206_;
v___y_4162_ = v___y_4208_;
v___y_4163_ = v___y_4211_;
v___y_4164_ = v___y_4224_;
v___y_4165_ = v___y_4212_;
v___y_4166_ = v___y_4222_;
v___y_4167_ = v_leLvl_4219_;
v___y_4168_ = v___y_4213_;
v___y_4169_ = v___y_4214_;
v___y_4170_ = v___y_4225_;
v___y_4171_ = v___y_4217_;
v___y_4172_ = v___y_4201_;
v___y_4173_ = v___y_4202_;
v___y_4174_ = v___y_4220_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4209_;
v___y_4177_ = v___y_4210_;
v___y_4178_ = v___y_4221_;
v___y_4179_ = v___y_4215_;
v___y_4180_ = v___y_4226_;
v___y_4181_ = v___y_4223_;
v___y_4182_ = v___y_4218_;
v_a_4183_ = v___y_4217_;
goto v___jp_4157_;
}
else
{
lean_object* v_val_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v_val_4227_ = lean_ctor_get(v___y_4217_, 0);
v___x_4228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v___y_4216_);
v___x_4229_ = l_Lean_Name_mkStr2(v___y_4216_, v___x_4228_);
lean_inc(v___y_4214_);
lean_inc(v_leLvl_4219_);
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_leLvl_4219_);
lean_ctor_set(v___x_4230_, 1, v___y_4214_);
v___x_4231_ = l_Lean_mkConst(v___x_4229_, v___x_4230_);
lean_inc(v_val_4227_);
lean_inc_ref(v_type_4067_);
v___x_4232_ = l_Lean_mkAppB(v___x_4231_, v_type_4067_, v_val_4227_);
v___x_4233_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4232_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4235_, 0, v_a_4234_);
v___y_4158_ = v___y_4203_;
v___y_4159_ = v___y_4204_;
v___y_4160_ = v___y_4205_;
v___y_4161_ = v___y_4206_;
v___y_4162_ = v___y_4208_;
v___y_4163_ = v___y_4211_;
v___y_4164_ = v___y_4224_;
v___y_4165_ = v___y_4212_;
v___y_4166_ = v___y_4222_;
v___y_4167_ = v_leLvl_4219_;
v___y_4168_ = v___y_4213_;
v___y_4169_ = v___y_4214_;
v___y_4170_ = v___y_4225_;
v___y_4171_ = v___y_4217_;
v___y_4172_ = v___y_4201_;
v___y_4173_ = v___y_4202_;
v___y_4174_ = v___y_4220_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4209_;
v___y_4177_ = v___y_4210_;
v___y_4178_ = v___y_4221_;
v___y_4179_ = v___y_4215_;
v___y_4180_ = v___y_4226_;
v___y_4181_ = v___y_4223_;
v___y_4182_ = v___y_4218_;
v_a_4183_ = v___x_4235_;
goto v___jp_4157_;
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref_known(v___y_4217_, 1);
lean_dec(v_leLvl_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4236_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4233_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4233_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
v___jp_4244_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11));
lean_inc_ref(v___y_4257_);
v___x_4286_ = l_Lean_Name_mkStr2(v___y_4257_, v___x_4285_);
lean_inc(v___y_4269_);
v___x_4287_ = l_Lean_mkConst(v___x_4286_, v___y_4269_);
lean_inc_ref(v_type_4067_);
v___x_4288_ = l_Lean_mkAppB(v___x_4287_, v_type_4067_, v___y_4256_);
v___x_4289_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
v___x_4291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc_ref(v___y_4258_);
v___x_4292_ = l_Lean_Name_mkStr2(v___y_4258_, v___x_4291_);
lean_inc(v___y_4269_);
v___x_4293_ = l_Lean_mkConst(v___x_4292_, v___y_4269_);
lean_inc_ref(v_type_4067_);
v___x_4294_ = l_Lean_mkApp3(v___x_4293_, v_type_4067_, v___y_4271_, v___y_4251_);
v___x_4295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4294_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57));
lean_inc_ref(v___y_4254_);
v___x_4298_ = l_Lean_Name_mkStr2(v___y_4254_, v___x_4297_);
lean_inc(v___y_4268_);
v___x_4299_ = l_Lean_mkConst(v___x_4298_, v___y_4268_);
lean_inc_ref_n(v_type_4067_, 3);
v___x_4300_ = l_Lean_mkApp4(v___x_4299_, v_type_4067_, v_type_4067_, v_type_4067_, v___y_4273_);
v___x_4301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4300_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_4259_);
v___x_4304_ = l_Lean_Name_mkStr2(v___y_4259_, v___x_4303_);
v___x_4305_ = l_Lean_mkConst(v___x_4304_, v___y_4268_);
lean_inc_ref_n(v_type_4067_, 3);
v___x_4306_ = l_Lean_mkApp4(v___x_4305_, v_type_4067_, v_type_4067_, v_type_4067_, v___y_4264_);
v___x_4307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4306_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_4250_);
v___x_4310_ = l_Lean_Name_mkStr2(v___y_4250_, v___x_4309_);
v___x_4311_ = l_Lean_mkConst(v___x_4310_, v___y_4269_);
lean_inc_ref(v_type_4067_);
v___x_4312_ = l_Lean_mkAppB(v___x_4311_, v_type_4067_, v___y_4249_);
v___x_4313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4312_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_4260_);
v___x_4316_ = l_Lean_Name_mkStr2(v___y_4260_, v___x_4315_);
v___x_4317_ = l_Lean_mkConst(v___x_4316_, v___y_4247_);
lean_inc_ref_n(v_type_4067_, 2);
lean_inc_ref(v___x_4317_);
v___x_4318_ = l_Lean_mkApp4(v___x_4317_, v___y_4263_, v_type_4067_, v_type_4067_, v___y_4261_);
v___x_4319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4318_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
lean_inc_ref_n(v_type_4067_, 2);
v___x_4321_ = l_Lean_mkApp4(v___x_4317_, v___y_4262_, v_type_4067_, v_type_4067_, v___y_4267_);
v___x_4322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4321_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4324_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4322_, 1);
v___x_4324_ = l_Lean_leCarrierIsSort(v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; uint8_t v___x_4326_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = lean_unbox(v_a_4325_);
lean_dec(v_a_4325_);
if (v___x_4326_ == 0)
{
lean_inc(v_val_4086_);
v___y_4201_ = v_a_4290_;
v___y_4202_ = v_a_4308_;
v___y_4203_ = v___y_4245_;
v___y_4204_ = v_a_4302_;
v___y_4205_ = v___y_4246_;
v___y_4206_ = v_a_4296_;
v___y_4207_ = v_a_4323_;
v___y_4208_ = v_a_4320_;
v___y_4209_ = v___y_4265_;
v___y_4210_ = v___y_4266_;
v___y_4211_ = v___y_4248_;
v___y_4212_ = v_a_4314_;
v___y_4213_ = v___y_4252_;
v___y_4214_ = v___y_4253_;
v___y_4215_ = v___y_4270_;
v___y_4216_ = v___y_4272_;
v___y_4217_ = v___y_4255_;
v___y_4218_ = v___y_4274_;
v_leLvl_4219_ = v_val_4086_;
v___y_4220_ = v___y_4275_;
v___y_4221_ = v___y_4279_;
v___y_4222_ = v___y_4280_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4282_;
v___y_4225_ = v___y_4283_;
v___y_4226_ = v___y_4284_;
goto v___jp_4200_;
}
else
{
lean_object* v___x_4327_; 
lean_inc(v_val_4086_);
v___x_4327_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_4201_ = v_a_4290_;
v___y_4202_ = v_a_4308_;
v___y_4203_ = v___y_4245_;
v___y_4204_ = v_a_4302_;
v___y_4205_ = v___y_4246_;
v___y_4206_ = v_a_4296_;
v___y_4207_ = v_a_4323_;
v___y_4208_ = v_a_4320_;
v___y_4209_ = v___y_4265_;
v___y_4210_ = v___y_4266_;
v___y_4211_ = v___y_4248_;
v___y_4212_ = v_a_4314_;
v___y_4213_ = v___y_4252_;
v___y_4214_ = v___y_4253_;
v___y_4215_ = v___y_4270_;
v___y_4216_ = v___y_4272_;
v___y_4217_ = v___y_4255_;
v___y_4218_ = v___y_4274_;
v_leLvl_4219_ = v___x_4327_;
v___y_4220_ = v___y_4275_;
v___y_4221_ = v___y_4279_;
v___y_4222_ = v___y_4280_;
v___y_4223_ = v___y_4281_;
v___y_4224_ = v___y_4282_;
v___y_4225_ = v___y_4283_;
v___y_4226_ = v___y_4284_;
goto v___jp_4200_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_a_4323_);
lean_dec(v_a_4320_);
lean_dec(v_a_4314_);
lean_dec(v_a_4308_);
lean_dec(v_a_4302_);
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec(v___y_4248_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4328_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4324_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4324_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4314_);
lean_dec(v_a_4308_);
lean_dec(v_a_4302_);
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec(v___y_4248_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4336_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4322_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4322_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec_ref(v___x_4317_);
lean_dec(v_a_4314_);
lean_dec(v_a_4308_);
lean_dec(v_a_4302_);
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec(v___y_4248_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4344_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4319_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4319_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v_a_4308_);
lean_dec(v_a_4302_);
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4352_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4313_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4313_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_a_4302_);
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4360_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4307_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4307_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec(v_a_4296_);
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4368_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4301_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4301_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_a_4290_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4376_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4295_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4295_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4255_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4384_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4289_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4289_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
v___jp_4392_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4401_);
v___x_4436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4436_, 0, v_____do__lift_4424_);
lean_ctor_set(v___x_4436_, 1, v___y_4401_);
v___x_4437_ = l_Lean_mkConst(v___x_4435_, v___x_4436_);
lean_inc_ref(v_type_4067_);
v___x_4438_ = l_Lean_Expr_app___override(v___x_4437_, v_type_4067_);
v___x_4439_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4438_, v___y_4418_, v___y_4430_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_dec_ref_known(v___x_4439_, 1);
v___y_4245_ = v___y_4393_;
v___y_4246_ = v___y_4394_;
v___y_4247_ = v___y_4395_;
v___y_4248_ = v___y_4396_;
v___y_4249_ = v___y_4397_;
v___y_4250_ = v___y_4399_;
v___y_4251_ = v___y_4398_;
v___y_4252_ = v___y_4400_;
v___y_4253_ = v___y_4401_;
v___y_4254_ = v___y_4402_;
v___y_4255_ = v___y_4404_;
v___y_4256_ = v___y_4403_;
v___y_4257_ = v___y_4405_;
v___y_4258_ = v___y_4406_;
v___y_4259_ = v___y_4407_;
v___y_4260_ = v___y_4408_;
v___y_4261_ = v___y_4409_;
v___y_4262_ = v___y_4410_;
v___y_4263_ = v___y_4411_;
v___y_4264_ = v___y_4412_;
v___y_4265_ = v___y_4413_;
v___y_4266_ = v___y_4414_;
v___y_4267_ = v___y_4415_;
v___y_4268_ = v___y_4416_;
v___y_4269_ = v___y_4417_;
v___y_4270_ = v___y_4419_;
v___y_4271_ = v___y_4420_;
v___y_4272_ = v___y_4421_;
v___y_4273_ = v___y_4422_;
v___y_4274_ = v___y_4423_;
v___y_4275_ = v___y_4425_;
v___y_4276_ = v___y_4426_;
v___y_4277_ = v___y_4427_;
v___y_4278_ = v___y_4428_;
v___y_4279_ = v___y_4429_;
v___y_4280_ = v___y_4430_;
v___y_4281_ = v___y_4431_;
v___y_4282_ = v___y_4432_;
v___y_4283_ = v___y_4433_;
v___y_4284_ = v___y_4434_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec_ref(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec(v___y_4393_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4439_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4439_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
v___jp_4448_:
{
if (lean_obj_tag(v___y_4470_) == 1)
{
lean_object* v_val_4489_; lean_object* v___x_4490_; 
v_val_4489_ = lean_ctor_get(v___y_4470_, 0);
lean_inc(v_val_4489_);
v___x_4490_ = l_Lean_leCarrierIsSort(v___y_4487_, v___y_4488_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; uint8_t v___x_4492_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v___x_4492_ = lean_unbox(v_a_4491_);
lean_dec(v_a_4491_);
if (v___x_4492_ == 0)
{
lean_inc(v_val_4086_);
v___y_4393_ = v___y_4449_;
v___y_4394_ = v___y_4450_;
v___y_4395_ = v___y_4451_;
v___y_4396_ = v___y_4452_;
v___y_4397_ = v___y_4453_;
v___y_4398_ = v___y_4455_;
v___y_4399_ = v___y_4454_;
v___y_4400_ = v___y_4456_;
v___y_4401_ = v___y_4457_;
v___y_4402_ = v___y_4458_;
v___y_4403_ = v___y_4460_;
v___y_4404_ = v___y_4459_;
v___y_4405_ = v___y_4461_;
v___y_4406_ = v___y_4462_;
v___y_4407_ = v___y_4463_;
v___y_4408_ = v___y_4464_;
v___y_4409_ = v___y_4465_;
v___y_4410_ = v___y_4466_;
v___y_4411_ = v___y_4467_;
v___y_4412_ = v___y_4468_;
v___y_4413_ = v___y_4469_;
v___y_4414_ = v___y_4470_;
v___y_4415_ = v___y_4471_;
v___y_4416_ = v___y_4472_;
v___y_4417_ = v___y_4473_;
v___y_4418_ = v_val_4489_;
v___y_4419_ = v___y_4474_;
v___y_4420_ = v___y_4475_;
v___y_4421_ = v___y_4476_;
v___y_4422_ = v___y_4477_;
v___y_4423_ = v___y_4478_;
v_____do__lift_4424_ = v_val_4086_;
v___y_4425_ = v___y_4479_;
v___y_4426_ = v___y_4480_;
v___y_4427_ = v___y_4481_;
v___y_4428_ = v___y_4482_;
v___y_4429_ = v___y_4483_;
v___y_4430_ = v___y_4484_;
v___y_4431_ = v___y_4485_;
v___y_4432_ = v___y_4486_;
v___y_4433_ = v___y_4487_;
v___y_4434_ = v___y_4488_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4493_; 
lean_inc(v_val_4086_);
v___x_4493_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_4393_ = v___y_4449_;
v___y_4394_ = v___y_4450_;
v___y_4395_ = v___y_4451_;
v___y_4396_ = v___y_4452_;
v___y_4397_ = v___y_4453_;
v___y_4398_ = v___y_4455_;
v___y_4399_ = v___y_4454_;
v___y_4400_ = v___y_4456_;
v___y_4401_ = v___y_4457_;
v___y_4402_ = v___y_4458_;
v___y_4403_ = v___y_4460_;
v___y_4404_ = v___y_4459_;
v___y_4405_ = v___y_4461_;
v___y_4406_ = v___y_4462_;
v___y_4407_ = v___y_4463_;
v___y_4408_ = v___y_4464_;
v___y_4409_ = v___y_4465_;
v___y_4410_ = v___y_4466_;
v___y_4411_ = v___y_4467_;
v___y_4412_ = v___y_4468_;
v___y_4413_ = v___y_4469_;
v___y_4414_ = v___y_4470_;
v___y_4415_ = v___y_4471_;
v___y_4416_ = v___y_4472_;
v___y_4417_ = v___y_4473_;
v___y_4418_ = v_val_4489_;
v___y_4419_ = v___y_4474_;
v___y_4420_ = v___y_4475_;
v___y_4421_ = v___y_4476_;
v___y_4422_ = v___y_4477_;
v___y_4423_ = v___y_4478_;
v_____do__lift_4424_ = v___x_4493_;
v___y_4425_ = v___y_4479_;
v___y_4426_ = v___y_4480_;
v___y_4427_ = v___y_4481_;
v___y_4428_ = v___y_4482_;
v___y_4429_ = v___y_4483_;
v___y_4430_ = v___y_4484_;
v___y_4431_ = v___y_4485_;
v___y_4432_ = v___y_4486_;
v___y_4433_ = v___y_4487_;
v___y_4434_ = v___y_4488_;
goto v___jp_4392_;
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref_known(v___y_4470_, 1);
lean_dec(v_val_4489_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec_ref(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec(v___y_4449_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4494_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4490_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4490_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
v___y_4245_ = v___y_4449_;
v___y_4246_ = v___y_4450_;
v___y_4247_ = v___y_4451_;
v___y_4248_ = v___y_4452_;
v___y_4249_ = v___y_4453_;
v___y_4250_ = v___y_4454_;
v___y_4251_ = v___y_4455_;
v___y_4252_ = v___y_4456_;
v___y_4253_ = v___y_4457_;
v___y_4254_ = v___y_4458_;
v___y_4255_ = v___y_4459_;
v___y_4256_ = v___y_4460_;
v___y_4257_ = v___y_4461_;
v___y_4258_ = v___y_4462_;
v___y_4259_ = v___y_4463_;
v___y_4260_ = v___y_4464_;
v___y_4261_ = v___y_4465_;
v___y_4262_ = v___y_4466_;
v___y_4263_ = v___y_4467_;
v___y_4264_ = v___y_4468_;
v___y_4265_ = v___y_4469_;
v___y_4266_ = v___y_4470_;
v___y_4267_ = v___y_4471_;
v___y_4268_ = v___y_4472_;
v___y_4269_ = v___y_4473_;
v___y_4270_ = v___y_4474_;
v___y_4271_ = v___y_4475_;
v___y_4272_ = v___y_4476_;
v___y_4273_ = v___y_4477_;
v___y_4274_ = v___y_4478_;
v___y_4275_ = v___y_4479_;
v___y_4276_ = v___y_4480_;
v___y_4277_ = v___y_4481_;
v___y_4278_ = v___y_4482_;
v___y_4279_ = v___y_4483_;
v___y_4280_ = v___y_4484_;
v___y_4281_ = v___y_4485_;
v___y_4282_ = v___y_4486_;
v___y_4283_ = v___y_4487_;
v___y_4284_ = v___y_4488_;
goto v___jp_4244_;
}
}
v___jp_4502_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
lean_inc(v___y_4511_);
v___x_4546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4546_, 0, v_____do__lift_4535_);
lean_ctor_set(v___x_4546_, 1, v___y_4511_);
v___x_4547_ = l_Lean_mkConst(v___y_4512_, v___x_4546_);
lean_inc_ref(v_type_4067_);
v___x_4548_ = l_Lean_Expr_app___override(v___x_4547_, v_type_4067_);
v___x_4549_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4548_, v___y_4523_, v___y_4541_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_dec_ref_known(v___x_4549_, 1);
v___y_4449_ = v___y_4503_;
v___y_4450_ = v___y_4504_;
v___y_4451_ = v___y_4505_;
v___y_4452_ = v___y_4506_;
v___y_4453_ = v___y_4507_;
v___y_4454_ = v___y_4509_;
v___y_4455_ = v___y_4508_;
v___y_4456_ = v___y_4510_;
v___y_4457_ = v___y_4511_;
v___y_4458_ = v___y_4513_;
v___y_4459_ = v___y_4514_;
v___y_4460_ = v___y_4515_;
v___y_4461_ = v___y_4516_;
v___y_4462_ = v___y_4517_;
v___y_4463_ = v___y_4518_;
v___y_4464_ = v___y_4519_;
v___y_4465_ = v___y_4520_;
v___y_4466_ = v___y_4521_;
v___y_4467_ = v___y_4522_;
v___y_4468_ = v___y_4524_;
v___y_4469_ = v___y_4525_;
v___y_4470_ = v___y_4526_;
v___y_4471_ = v___y_4527_;
v___y_4472_ = v___y_4528_;
v___y_4473_ = v___y_4529_;
v___y_4474_ = v___y_4530_;
v___y_4475_ = v___y_4531_;
v___y_4476_ = v___y_4532_;
v___y_4477_ = v___y_4533_;
v___y_4478_ = v___y_4534_;
v___y_4479_ = v___y_4536_;
v___y_4480_ = v___y_4537_;
v___y_4481_ = v___y_4538_;
v___y_4482_ = v___y_4539_;
v___y_4483_ = v___y_4540_;
v___y_4484_ = v___y_4541_;
v___y_4485_ = v___y_4542_;
v___y_4486_ = v___y_4543_;
v___y_4487_ = v___y_4544_;
v___y_4488_ = v___y_4545_;
goto v___jp_4448_;
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4557_; 
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec(v___y_4503_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4552_ = v___x_4549_;
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4549_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4557_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4555_; 
if (v_isShared_4553_ == 0)
{
v___x_4555_ = v___x_4552_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4550_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
}
v___jp_4558_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
lean_inc_n(v___y_4560_, 14);
v___x_4581_ = l_Lean_mkConst(v___x_4580_, v___y_4560_);
v___x_4582_ = l_Lean_mkAppB(v___x_4581_, v_base_4068_, v_natModuleInst_4069_);
v___x_4583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49));
v___x_4584_ = l_Lean_mkConst(v___x_4583_, v___y_4560_);
lean_inc_ref_n(v___x_4582_, 4);
lean_inc_ref_n(v_type_4067_, 14);
v___x_4585_ = l_Lean_mkAppB(v___x_4584_, v_type_4067_, v___x_4582_);
v___x_4586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52));
v___x_4587_ = l_Lean_mkConst(v___x_4586_, v___y_4560_);
lean_inc_ref_n(v___x_4585_, 2);
v___x_4588_ = l_Lean_mkAppB(v___x_4587_, v_type_4067_, v___x_4585_);
v___x_4589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4));
v___x_4590_ = l_Lean_mkConst(v___x_4589_, v___y_4560_);
lean_inc_ref(v___x_4588_);
v___x_4591_ = l_Lean_mkAppB(v___x_4590_, v_type_4067_, v___x_4588_);
v___x_4592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9));
v___x_4593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4594_ = l_Lean_mkConst(v___x_4593_, v___y_4560_);
lean_inc_ref(v___x_4591_);
v___x_4595_ = l_Lean_mkAppB(v___x_4594_, v_type_4067_, v___x_4591_);
v___x_4596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_4597_ = l_Lean_mkConst(v___x_4596_, v___y_4560_);
v___x_4598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4599_ = l_Lean_mkConst(v___x_4598_, v___y_4560_);
v___x_4600_ = l_Lean_mkAppB(v___x_4599_, v_type_4067_, v___x_4588_);
v___x_4601_ = l_Lean_mkAppB(v___x_4597_, v_type_4067_, v___x_4600_);
v___x_4602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33));
v___x_4603_ = l_Lean_mkConst(v___x_4602_, v___y_4560_);
v___x_4604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4605_ = l_Lean_mkConst(v___x_4604_, v___y_4560_);
v___x_4606_ = l_Lean_mkAppB(v___x_4605_, v_type_4067_, v___x_4585_);
v___x_4607_ = l_Lean_mkAppB(v___x_4603_, v_type_4067_, v___x_4606_);
v___x_4608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4609_ = l_Lean_mkConst(v___x_4608_, v___y_4560_);
v___x_4610_ = l_Lean_mkAppB(v___x_4609_, v_type_4067_, v___x_4585_);
v___x_4611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4612_ = lean_unsigned_to_nat(0u);
v___x_4613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
lean_ctor_set(v___x_4614_, 1, v___y_4560_);
v___x_4615_ = l_Lean_mkConst(v___x_4611_, v___x_4614_);
v___x_4616_ = l_Lean_Int_mkType;
v___x_4617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4618_ = l_Lean_mkConst(v___x_4617_, v___y_4560_);
v___x_4619_ = l_Lean_mkAppB(v___x_4618_, v_type_4067_, v___x_4582_);
lean_inc_ref(v___x_4615_);
v___x_4620_ = l_Lean_mkApp3(v___x_4615_, v___x_4616_, v_type_4067_, v___x_4619_);
v___x_4621_ = l_Lean_Nat_mkType;
v___x_4622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11));
v___x_4623_ = l_Lean_mkConst(v___x_4622_, v___y_4560_);
v___x_4624_ = l_Lean_mkAppB(v___x_4623_, v_type_4067_, v___x_4582_);
v___x_4625_ = l_Lean_mkApp3(v___x_4615_, v___x_4621_, v_type_4067_, v___x_4624_);
v___x_4626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4627_ = l_Lean_mkConst(v___x_4626_, v___y_4560_);
v___x_4628_ = l_Lean_Expr_app___override(v___x_4627_, v_type_4067_);
v___x_4629_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4628_, v___x_4582_, v___y_4575_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
lean_dec_ref_known(v___x_4629_, 1);
v___x_4630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc(v___y_4560_);
v___x_4631_ = l_Lean_mkConst(v___x_4630_, v___y_4560_);
lean_inc_ref(v_type_4067_);
v___x_4632_ = l_Lean_Expr_app___override(v___x_4631_, v_type_4067_);
lean_inc_ref(v___x_4591_);
v___x_4633_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4632_, v___x_4591_, v___y_4575_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
lean_dec_ref_known(v___x_4633_, 1);
v___x_4634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4560_);
v___x_4636_ = l_Lean_mkConst(v___x_4635_, v___y_4560_);
v___x_4637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15);
lean_inc_ref(v_type_4067_);
v___x_4638_ = l_Lean_mkAppB(v___x_4636_, v_type_4067_, v___x_4637_);
lean_inc_ref(v___x_4595_);
v___x_4639_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4638_, v___x_4595_, v___y_4575_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
lean_dec_ref_known(v___x_4639_, 1);
v___x_4640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc(v___y_4560_);
lean_inc_n(v_val_4086_, 2);
v___x_4642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4642_, 0, v_val_4086_);
lean_ctor_set(v___x_4642_, 1, v___y_4560_);
lean_inc_ref(v___x_4642_);
v___x_4643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4643_, 0, v_val_4086_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
lean_inc_ref(v___x_4643_);
v___x_4644_ = l_Lean_mkConst(v___x_4641_, v___x_4643_);
lean_inc_ref_n(v_type_4067_, 3);
v___x_4645_ = l_Lean_mkApp3(v___x_4644_, v_type_4067_, v_type_4067_, v_type_4067_);
lean_inc_ref(v___x_4601_);
v___x_4646_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4645_, v___x_4601_, v___y_4575_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
lean_dec_ref_known(v___x_4646_, 1);
v___x_4647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
v___x_4648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19));
lean_inc_ref(v___x_4643_);
v___x_4649_ = l_Lean_mkConst(v___x_4648_, v___x_4643_);
lean_inc_ref_n(v_type_4067_, 3);
v___x_4650_ = l_Lean_mkApp3(v___x_4649_, v_type_4067_, v_type_4067_, v_type_4067_);
lean_inc_ref(v___x_4607_);
v___x_4651_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4650_, v___x_4607_, v___y_4575_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
lean_dec_ref_known(v___x_4651_, 1);
v___x_4652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc(v___y_4560_);
v___x_4654_ = l_Lean_mkConst(v___x_4653_, v___y_4560_);
lean_inc_ref(v_type_4067_);
v___x_4655_ = l_Lean_Expr_app___override(v___x_4654_, v_type_4067_);
lean_inc_ref(v___x_4610_);
v___x_4656_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4655_, v___x_4610_, v___y_4575_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
lean_dec_ref_known(v___x_4656_, 1);
v___x_4657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4613_);
lean_ctor_set(v___x_4659_, 1, v___x_4642_);
lean_inc_ref(v___x_4659_);
v___x_4660_ = l_Lean_mkConst(v___x_4658_, v___x_4659_);
lean_inc_ref_n(v_type_4067_, 2);
lean_inc_ref(v___x_4660_);
v___x_4661_ = l_Lean_mkApp3(v___x_4660_, v___x_4616_, v_type_4067_, v_type_4067_);
lean_inc_ref(v___x_4620_);
v___x_4662_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4661_, v___x_4620_, v___y_4575_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
lean_dec_ref_known(v___x_4662_, 1);
lean_inc_ref_n(v_type_4067_, 2);
v___x_4663_ = l_Lean_mkApp3(v___x_4660_, v___x_4621_, v_type_4067_, v_type_4067_);
lean_inc_ref(v___x_4625_);
v___x_4664_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4663_, v___x_4625_, v___y_4575_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_dec_ref_known(v___x_4664_, 1);
if (lean_obj_tag(v___y_4566_) == 1)
{
lean_object* v_val_4665_; lean_object* v___x_4666_; 
v_val_4665_ = lean_ctor_get(v___y_4566_, 0);
lean_inc(v_val_4665_);
v___x_4666_ = l_Lean_leCarrierIsSort(v___y_4578_, v___y_4579_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; uint8_t v___x_4668_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref_known(v___x_4666_, 1);
v___x_4668_ = lean_unbox(v_a_4667_);
lean_dec(v_a_4667_);
if (v___x_4668_ == 0)
{
lean_inc(v_val_4086_);
v___y_4503_ = v_noNatDivInstQ_x3f_4569_;
v___y_4504_ = v___x_4612_;
v___y_4505_ = v___x_4659_;
v___y_4506_ = v___y_4567_;
v___y_4507_ = v___x_4610_;
v___y_4508_ = v___x_4595_;
v___y_4509_ = v___x_4652_;
v___y_4510_ = v___y_4559_;
v___y_4511_ = v___y_4561_;
v___y_4512_ = v___y_4562_;
v___y_4513_ = v___x_4640_;
v___y_4514_ = v___y_4566_;
v___y_4515_ = v___x_4591_;
v___y_4516_ = v___x_4592_;
v___y_4517_ = v___x_4634_;
v___y_4518_ = v___x_4647_;
v___y_4519_ = v___x_4657_;
v___y_4520_ = v___x_4620_;
v___y_4521_ = v___x_4621_;
v___y_4522_ = v___x_4616_;
v___y_4523_ = v_val_4665_;
v___y_4524_ = v___x_4607_;
v___y_4525_ = v___y_4563_;
v___y_4526_ = v___y_4565_;
v___y_4527_ = v___x_4625_;
v___y_4528_ = v___x_4643_;
v___y_4529_ = v___y_4560_;
v___y_4530_ = v___x_4582_;
v___y_4531_ = v___x_4637_;
v___y_4532_ = v___y_4564_;
v___y_4533_ = v___x_4601_;
v___y_4534_ = v___y_4568_;
v_____do__lift_4535_ = v_val_4086_;
v___y_4536_ = v___y_4570_;
v___y_4537_ = v___y_4571_;
v___y_4538_ = v___y_4572_;
v___y_4539_ = v___y_4573_;
v___y_4540_ = v___y_4574_;
v___y_4541_ = v___y_4575_;
v___y_4542_ = v___y_4576_;
v___y_4543_ = v___y_4577_;
v___y_4544_ = v___y_4578_;
v___y_4545_ = v___y_4579_;
goto v___jp_4502_;
}
else
{
lean_object* v___x_4669_; 
lean_inc(v_val_4086_);
v___x_4669_ = l_Lean_Level_succ___override(v_val_4086_);
v___y_4503_ = v_noNatDivInstQ_x3f_4569_;
v___y_4504_ = v___x_4612_;
v___y_4505_ = v___x_4659_;
v___y_4506_ = v___y_4567_;
v___y_4507_ = v___x_4610_;
v___y_4508_ = v___x_4595_;
v___y_4509_ = v___x_4652_;
v___y_4510_ = v___y_4559_;
v___y_4511_ = v___y_4561_;
v___y_4512_ = v___y_4562_;
v___y_4513_ = v___x_4640_;
v___y_4514_ = v___y_4566_;
v___y_4515_ = v___x_4591_;
v___y_4516_ = v___x_4592_;
v___y_4517_ = v___x_4634_;
v___y_4518_ = v___x_4647_;
v___y_4519_ = v___x_4657_;
v___y_4520_ = v___x_4620_;
v___y_4521_ = v___x_4621_;
v___y_4522_ = v___x_4616_;
v___y_4523_ = v_val_4665_;
v___y_4524_ = v___x_4607_;
v___y_4525_ = v___y_4563_;
v___y_4526_ = v___y_4565_;
v___y_4527_ = v___x_4625_;
v___y_4528_ = v___x_4643_;
v___y_4529_ = v___y_4560_;
v___y_4530_ = v___x_4582_;
v___y_4531_ = v___x_4637_;
v___y_4532_ = v___y_4564_;
v___y_4533_ = v___x_4601_;
v___y_4534_ = v___y_4568_;
v_____do__lift_4535_ = v___x_4669_;
v___y_4536_ = v___y_4570_;
v___y_4537_ = v___y_4571_;
v___y_4538_ = v___y_4572_;
v___y_4539_ = v___y_4573_;
v___y_4540_ = v___y_4574_;
v___y_4541_ = v___y_4575_;
v___y_4542_ = v___y_4576_;
v___y_4543_ = v___y_4577_;
v___y_4544_ = v___y_4578_;
v___y_4545_ = v___y_4579_;
goto v___jp_4502_;
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec(v_val_4665_);
lean_dec_ref_known(v___y_4566_, 1);
lean_dec_ref_known(v___x_4659_, 2);
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4670_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4666_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4666_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
else
{
lean_dec(v___y_4562_);
v___y_4449_ = v_noNatDivInstQ_x3f_4569_;
v___y_4450_ = v___x_4612_;
v___y_4451_ = v___x_4659_;
v___y_4452_ = v___y_4567_;
v___y_4453_ = v___x_4610_;
v___y_4454_ = v___x_4652_;
v___y_4455_ = v___x_4595_;
v___y_4456_ = v___y_4559_;
v___y_4457_ = v___y_4561_;
v___y_4458_ = v___x_4640_;
v___y_4459_ = v___y_4566_;
v___y_4460_ = v___x_4591_;
v___y_4461_ = v___x_4592_;
v___y_4462_ = v___x_4634_;
v___y_4463_ = v___x_4647_;
v___y_4464_ = v___x_4657_;
v___y_4465_ = v___x_4620_;
v___y_4466_ = v___x_4621_;
v___y_4467_ = v___x_4616_;
v___y_4468_ = v___x_4607_;
v___y_4469_ = v___y_4563_;
v___y_4470_ = v___y_4565_;
v___y_4471_ = v___x_4625_;
v___y_4472_ = v___x_4643_;
v___y_4473_ = v___y_4560_;
v___y_4474_ = v___x_4582_;
v___y_4475_ = v___x_4637_;
v___y_4476_ = v___y_4564_;
v___y_4477_ = v___x_4601_;
v___y_4478_ = v___y_4568_;
v___y_4479_ = v___y_4570_;
v___y_4480_ = v___y_4571_;
v___y_4481_ = v___y_4572_;
v___y_4482_ = v___y_4573_;
v___y_4483_ = v___y_4574_;
v___y_4484_ = v___y_4575_;
v___y_4485_ = v___y_4576_;
v___y_4486_ = v___y_4577_;
v___y_4487_ = v___y_4578_;
v___y_4488_ = v___y_4579_;
goto v___jp_4448_;
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec_ref_known(v___x_4659_, 2);
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4678_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4664_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4664_);
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
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec_ref(v___x_4660_);
lean_dec_ref_known(v___x_4659_, 2);
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4686_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4662_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4662_);
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
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref_known(v___x_4642_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4694_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4656_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4656_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref_known(v___x_4642_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4702_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4651_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4651_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec_ref_known(v___x_4643_, 2);
lean_dec_ref_known(v___x_4642_, 2);
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4710_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4646_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4646_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4718_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4639_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4639_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4726_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4633_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4633_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___x_4591_);
lean_dec_ref(v___x_4582_);
lean_dec(v_noNatDivInstQ_x3f_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4560_);
lean_dec(v___y_4559_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_type_4067_);
v_a_4734_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4629_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4629_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
v___jp_4742_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13));
v___x_4762_ = lean_box(0);
lean_inc(v_val_4086_);
v___x_4763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4763_, 0, v_val_4086_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
lean_inc_ref(v___x_4763_);
v___x_4764_ = l_Lean_mkConst(v___x_4761_, v___x_4763_);
lean_inc_ref(v_base_4068_);
v___x_4765_ = l_Lean_Expr_app___override(v___x_4764_, v_base_4068_);
v___x_4766_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4765_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref_known(v___x_4766_, 1);
if (lean_obj_tag(v_a_4767_) == 1)
{
lean_object* v_val_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_val_4768_ = lean_ctor_get(v_a_4767_, 0);
lean_inc(v_val_4768_);
lean_dec_ref_known(v_a_4767_, 1);
v___x_4769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15));
lean_inc_ref(v___x_4763_);
v___x_4770_ = l_Lean_mkConst(v___x_4769_, v___x_4763_);
lean_inc_ref(v_base_4068_);
v___x_4771_ = l_Lean_mkAppB(v___x_4770_, v_base_4068_, v_val_4768_);
v___x_4772_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4771_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref_known(v___x_4772_, 1);
if (lean_obj_tag(v_a_4773_) == 1)
{
lean_object* v_val_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v_val_4774_ = lean_ctor_get(v_a_4773_, 0);
lean_inc(v_val_4774_);
lean_dec_ref_known(v_a_4773_, 1);
v___x_4775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4763_);
v___x_4776_ = l_Lean_mkConst(v___x_4775_, v___x_4763_);
lean_inc_ref(v_natModuleInst_4069_);
lean_inc_ref(v_base_4068_);
v___x_4777_ = l_Lean_mkAppB(v___x_4776_, v_base_4068_, v_natModuleInst_4069_);
v___x_4778_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4777_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref_known(v___x_4778_, 1);
if (lean_obj_tag(v_a_4779_) == 1)
{
lean_object* v_val_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4790_; 
v_val_4780_ = lean_ctor_get(v_a_4779_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_a_4779_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4782_ = v_a_4779_;
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_val_4780_);
lean_dec(v_a_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17));
lean_inc_ref(v___x_4763_);
v___x_4785_ = l_Lean_mkConst(v___x_4784_, v___x_4763_);
lean_inc_ref(v_natModuleInst_4069_);
lean_inc_ref(v_base_4068_);
v___x_4786_ = l_Lean_mkApp4(v___x_4785_, v_base_4068_, v_natModuleInst_4069_, v_val_4774_, v_val_4780_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4786_);
v___x_4788_ = v___x_4782_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
v___y_4559_ = v_isLinearInstQ_x3f_4750_;
v___y_4560_ = v___x_4763_;
v___y_4561_ = v___x_4762_;
v___y_4562_ = v___y_4743_;
v___y_4563_ = v___y_4744_;
v___y_4564_ = v___y_4745_;
v___y_4565_ = v___y_4746_;
v___y_4566_ = v___y_4748_;
v___y_4567_ = v___y_4747_;
v___y_4568_ = v___y_4749_;
v_noNatDivInstQ_x3f_4569_ = v___x_4788_;
v___y_4570_ = v___y_4751_;
v___y_4571_ = v___y_4752_;
v___y_4572_ = v___y_4753_;
v___y_4573_ = v___y_4754_;
v___y_4574_ = v___y_4755_;
v___y_4575_ = v___y_4756_;
v___y_4576_ = v___y_4757_;
v___y_4577_ = v___y_4758_;
v___y_4578_ = v___y_4759_;
v___y_4579_ = v___y_4760_;
goto v___jp_4558_;
}
}
}
else
{
lean_object* v___x_4791_; 
lean_dec(v_a_4779_);
lean_dec(v_val_4774_);
v___x_4791_ = lean_box(0);
v___y_4559_ = v_isLinearInstQ_x3f_4750_;
v___y_4560_ = v___x_4763_;
v___y_4561_ = v___x_4762_;
v___y_4562_ = v___y_4743_;
v___y_4563_ = v___y_4744_;
v___y_4564_ = v___y_4745_;
v___y_4565_ = v___y_4746_;
v___y_4566_ = v___y_4748_;
v___y_4567_ = v___y_4747_;
v___y_4568_ = v___y_4749_;
v_noNatDivInstQ_x3f_4569_ = v___x_4791_;
v___y_4570_ = v___y_4751_;
v___y_4571_ = v___y_4752_;
v___y_4572_ = v___y_4753_;
v___y_4573_ = v___y_4754_;
v___y_4574_ = v___y_4755_;
v___y_4575_ = v___y_4756_;
v___y_4576_ = v___y_4757_;
v___y_4577_ = v___y_4758_;
v___y_4578_ = v___y_4759_;
v___y_4579_ = v___y_4760_;
goto v___jp_4558_;
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_val_4774_);
lean_dec_ref_known(v___x_4763_, 2);
lean_dec(v_isLinearInstQ_x3f_4750_);
lean_dec(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec(v___y_4744_);
lean_dec(v___y_4743_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4792_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4778_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4778_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
else
{
lean_object* v___x_4800_; 
lean_dec(v_a_4773_);
v___x_4800_ = lean_box(0);
v___y_4559_ = v_isLinearInstQ_x3f_4750_;
v___y_4560_ = v___x_4763_;
v___y_4561_ = v___x_4762_;
v___y_4562_ = v___y_4743_;
v___y_4563_ = v___y_4744_;
v___y_4564_ = v___y_4745_;
v___y_4565_ = v___y_4746_;
v___y_4566_ = v___y_4748_;
v___y_4567_ = v___y_4747_;
v___y_4568_ = v___y_4749_;
v_noNatDivInstQ_x3f_4569_ = v___x_4800_;
v___y_4570_ = v___y_4751_;
v___y_4571_ = v___y_4752_;
v___y_4572_ = v___y_4753_;
v___y_4573_ = v___y_4754_;
v___y_4574_ = v___y_4755_;
v___y_4575_ = v___y_4756_;
v___y_4576_ = v___y_4757_;
v___y_4577_ = v___y_4758_;
v___y_4578_ = v___y_4759_;
v___y_4579_ = v___y_4760_;
goto v___jp_4558_;
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec_ref_known(v___x_4763_, 2);
lean_dec(v_isLinearInstQ_x3f_4750_);
lean_dec(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec(v___y_4744_);
lean_dec(v___y_4743_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4801_ = lean_ctor_get(v___x_4772_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4772_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4772_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v___x_4809_; 
lean_dec(v_a_4767_);
v___x_4809_ = lean_box(0);
v___y_4559_ = v_isLinearInstQ_x3f_4750_;
v___y_4560_ = v___x_4763_;
v___y_4561_ = v___x_4762_;
v___y_4562_ = v___y_4743_;
v___y_4563_ = v___y_4744_;
v___y_4564_ = v___y_4745_;
v___y_4565_ = v___y_4746_;
v___y_4566_ = v___y_4748_;
v___y_4567_ = v___y_4747_;
v___y_4568_ = v___y_4749_;
v_noNatDivInstQ_x3f_4569_ = v___x_4809_;
v___y_4570_ = v___y_4751_;
v___y_4571_ = v___y_4752_;
v___y_4572_ = v___y_4753_;
v___y_4573_ = v___y_4754_;
v___y_4574_ = v___y_4755_;
v___y_4575_ = v___y_4756_;
v___y_4576_ = v___y_4757_;
v___y_4577_ = v___y_4758_;
v___y_4578_ = v___y_4759_;
v___y_4579_ = v___y_4760_;
goto v___jp_4558_;
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec_ref_known(v___x_4763_, 2);
lean_dec(v_isLinearInstQ_x3f_4750_);
lean_dec(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec(v___y_4744_);
lean_dec(v___y_4743_);
lean_del_object(v___x_4088_);
lean_dec(v_val_4086_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_4810_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4766_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4766_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5136_; 
lean_dec(v_a_4082_);
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v___x_5134_ = lean_box(0);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_5134_);
v___x_5136_ = v___x_4084_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5134_);
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
lean_dec_ref(v_natModuleInst_4069_);
lean_dec_ref(v_base_4068_);
lean_dec_ref(v_type_4067_);
v_a_5139_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_4081_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_4081_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_5147_, lean_object* v_base_5148_, lean_object* v_natModuleInst_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_5147_, v_base_5148_, v_natModuleInst_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
lean_dec(v_a_5157_);
lean_dec_ref(v_a_5156_);
lean_dec(v_a_5155_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
lean_dec(v_a_5151_);
lean_dec(v_a_5150_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; 
v___x_5181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_5182_ = lean_unsigned_to_nat(2u);
v___x_5183_ = l_Lean_Expr_isAppOfArity(v_type_5169_, v___x_5181_, v___x_5182_);
if (v___x_5183_ == 0)
{
lean_object* v___x_5184_; 
v___x_5184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5184_;
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5185_ = l_Lean_Expr_appFn_x21(v_type_5169_);
v___x_5186_ = l_Lean_Expr_appArg_x21(v___x_5185_);
lean_dec_ref(v___x_5185_);
v___x_5187_ = l_Lean_Expr_appArg_x21(v_type_5169_);
v___x_5188_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_5169_, v___x_5186_, v___x_5187_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
lean_dec(v_a_5199_);
lean_dec_ref(v_a_5198_);
lean_dec(v_a_5197_);
lean_dec_ref(v_a_5196_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec(v_a_5190_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_5202_, lean_object* v_a_5203_, lean_object* v_s_5204_){
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
v___x_5216_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_5206_, v_type_5202_, v_a_5203_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 1, v___x_5216_);
v___x_5218_ = v___x_5214_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_structs_5205_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5219_, 2, v_exprToStructId_5207_);
lean_ctor_set(v_reuseFailAlloc_5219_, 3, v_exprToStructIdEntries_5208_);
lean_ctor_set(v_reuseFailAlloc_5219_, 4, v_forbiddenNatModules_5209_);
lean_ctor_set(v_reuseFailAlloc_5219_, 5, v_natStructs_5210_);
lean_ctor_set(v_reuseFailAlloc_5219_, 6, v_natTypeIdOf_5211_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5221_, lean_object* v_vals_5222_, lean_object* v_i_5223_, lean_object* v_k_5224_){
_start:
{
lean_object* v___x_5225_; uint8_t v___x_5226_; 
v___x_5225_ = lean_array_get_size(v_keys_5221_);
v___x_5226_ = lean_nat_dec_lt(v_i_5223_, v___x_5225_);
if (v___x_5226_ == 0)
{
lean_object* v___x_5227_; 
lean_dec(v_i_5223_);
v___x_5227_ = lean_box(0);
return v___x_5227_;
}
else
{
lean_object* v_k_x27_5228_; size_t v___x_5229_; size_t v___x_5230_; uint8_t v___x_5231_; 
v_k_x27_5228_ = lean_array_fget_borrowed(v_keys_5221_, v_i_5223_);
v___x_5229_ = lean_ptr_addr(v_k_5224_);
v___x_5230_ = lean_ptr_addr(v_k_x27_5228_);
v___x_5231_ = lean_usize_dec_eq(v___x_5229_, v___x_5230_);
if (v___x_5231_ == 0)
{
lean_object* v___x_5232_; lean_object* v___x_5233_; 
v___x_5232_ = lean_unsigned_to_nat(1u);
v___x_5233_ = lean_nat_add(v_i_5223_, v___x_5232_);
lean_dec(v_i_5223_);
v_i_5223_ = v___x_5233_;
goto _start;
}
else
{
lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5235_ = lean_array_fget_borrowed(v_vals_5222_, v_i_5223_);
lean_dec(v_i_5223_);
lean_inc(v___x_5235_);
v___x_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
return v___x_5236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5237_, lean_object* v_vals_5238_, lean_object* v_i_5239_, lean_object* v_k_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5237_, v_vals_5238_, v_i_5239_, v_k_5240_);
lean_dec_ref(v_k_5240_);
lean_dec_ref(v_vals_5238_);
lean_dec_ref(v_keys_5237_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5242_, size_t v_x_5243_, lean_object* v_x_5244_){
_start:
{
if (lean_obj_tag(v_x_5242_) == 0)
{
lean_object* v_es_5245_; lean_object* v___x_5246_; size_t v___x_5247_; size_t v___x_5248_; lean_object* v_j_5249_; lean_object* v___x_5250_; 
v_es_5245_ = lean_ctor_get(v_x_5242_, 0);
v___x_5246_ = lean_box(2);
v___x_5247_ = ((size_t)31ULL);
v___x_5248_ = lean_usize_land(v_x_5243_, v___x_5247_);
v_j_5249_ = lean_usize_to_nat(v___x_5248_);
v___x_5250_ = lean_array_get_borrowed(v___x_5246_, v_es_5245_, v_j_5249_);
lean_dec(v_j_5249_);
switch(lean_obj_tag(v___x_5250_))
{
case 0:
{
lean_object* v_key_5251_; lean_object* v_val_5252_; size_t v___x_5253_; size_t v___x_5254_; uint8_t v___x_5255_; 
v_key_5251_ = lean_ctor_get(v___x_5250_, 0);
v_val_5252_ = lean_ctor_get(v___x_5250_, 1);
v___x_5253_ = lean_ptr_addr(v_x_5244_);
v___x_5254_ = lean_ptr_addr(v_key_5251_);
v___x_5255_ = lean_usize_dec_eq(v___x_5253_, v___x_5254_);
if (v___x_5255_ == 0)
{
lean_object* v___x_5256_; 
v___x_5256_ = lean_box(0);
return v___x_5256_;
}
else
{
lean_object* v___x_5257_; 
lean_inc(v_val_5252_);
v___x_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5257_, 0, v_val_5252_);
return v___x_5257_;
}
}
case 1:
{
lean_object* v_node_5258_; size_t v___x_5259_; size_t v___x_5260_; 
v_node_5258_ = lean_ctor_get(v___x_5250_, 0);
v___x_5259_ = ((size_t)5ULL);
v___x_5260_ = lean_usize_shift_right(v_x_5243_, v___x_5259_);
v_x_5242_ = v_node_5258_;
v_x_5243_ = v___x_5260_;
goto _start;
}
default: 
{
lean_object* v___x_5262_; 
v___x_5262_ = lean_box(0);
return v___x_5262_;
}
}
}
else
{
lean_object* v_ks_5263_; lean_object* v_vs_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
v_ks_5263_ = lean_ctor_get(v_x_5242_, 0);
v_vs_5264_ = lean_ctor_get(v_x_5242_, 1);
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5263_, v_vs_5264_, v___x_5265_, v_x_5244_);
return v___x_5266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5267_, lean_object* v_x_5268_, lean_object* v_x_5269_){
_start:
{
size_t v_x_8070__boxed_5270_; lean_object* v_res_5271_; 
v_x_8070__boxed_5270_ = lean_unbox_usize(v_x_5268_);
lean_dec(v_x_5268_);
v_res_5271_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5267_, v_x_8070__boxed_5270_, v_x_5269_);
lean_dec_ref(v_x_5269_);
lean_dec_ref(v_x_5267_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_5272_, lean_object* v_x_5273_){
_start:
{
size_t v___x_5274_; size_t v___x_5275_; size_t v___x_5276_; uint64_t v___x_5277_; size_t v___x_5278_; lean_object* v___x_5279_; 
v___x_5274_ = lean_ptr_addr(v_x_5273_);
v___x_5275_ = ((size_t)3ULL);
v___x_5276_ = lean_usize_shift_right(v___x_5274_, v___x_5275_);
v___x_5277_ = lean_usize_to_uint64(v___x_5276_);
v___x_5278_ = lean_uint64_to_usize(v___x_5277_);
v___x_5279_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5272_, v___x_5278_, v_x_5273_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5280_, lean_object* v_x_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_5280_, v_x_5281_);
lean_dec_ref(v_x_5281_);
lean_dec_ref(v_x_5280_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5286_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5365_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5298_ = v___x_5295_;
v_isShared_5299_ = v_isSharedCheck_5365_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5295_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5365_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
uint8_t v_linarith_5300_; 
v_linarith_5300_ = lean_ctor_get_uint8(v_a_5296_, sizeof(void*)*14 + 22);
lean_dec(v_a_5296_);
if (v_linarith_5300_ == 0)
{
lean_object* v___x_5301_; lean_object* v___x_5303_; 
lean_dec_ref(v_type_5283_);
v___x_5301_ = lean_box(0);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 0, v___x_5301_);
v___x_5303_ = v___x_5298_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
else
{
lean_object* v___x_5305_; 
lean_del_object(v___x_5298_);
lean_inc_ref(v_type_5283_);
v___x_5305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5356_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5308_ = v___x_5305_;
v_isShared_5309_ = v_isSharedCheck_5356_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5356_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_unbox(v_a_5306_);
lean_dec(v_a_5306_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; 
lean_del_object(v___x_5308_);
v___x_5311_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5284_, v_a_5292_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5343_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5314_ = v___x_5311_;
v_isShared_5315_ = v_isSharedCheck_5343_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5343_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v_typeIdOf_5316_; lean_object* v___x_5317_; 
v_typeIdOf_5316_ = lean_ctor_get(v_a_5312_, 1);
lean_inc_ref(v_typeIdOf_5316_);
lean_dec(v_a_5312_);
v___x_5317_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_5316_, v_type_5283_);
lean_dec_ref(v_typeIdOf_5316_);
if (lean_obj_tag(v___x_5317_) == 1)
{
lean_object* v_val_5318_; lean_object* v___x_5320_; 
lean_dec_ref(v_type_5283_);
v_val_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_val_5318_);
lean_dec_ref_known(v___x_5317_, 1);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v_val_5318_);
v___x_5320_ = v___x_5314_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_val_5318_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
else
{
lean_object* v___x_5322_; 
lean_dec(v___x_5317_);
lean_del_object(v___x_5314_);
lean_inc_ref(v_type_5283_);
v___x_5322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___f_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc_n(v_a_5323_, 2);
lean_dec_ref_known(v___x_5322_, 1);
v___f_5324_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5324_, 0, v_type_5283_);
lean_closure_set(v___f_5324_, 1, v_a_5323_);
v___x_5325_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5326_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5325_, v___f_5324_, v_a_5284_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5333_ == 0)
{
lean_object* v_unused_5334_; 
v_unused_5334_ = lean_ctor_get(v___x_5326_, 0);
lean_dec(v_unused_5334_);
v___x_5328_ = v___x_5326_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_dec(v___x_5326_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 0, v_a_5323_);
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5323_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
else
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
lean_dec(v_a_5323_);
v_a_5335_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5326_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5326_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
else
{
lean_dec_ref(v_type_5283_);
return v___x_5322_;
}
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec_ref(v_type_5283_);
v_a_5344_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5311_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5311_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
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
lean_object* v___x_5352_; lean_object* v___x_5354_; 
lean_dec_ref(v_type_5283_);
v___x_5352_ = lean_box(0);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5352_);
v___x_5354_ = v___x_5308_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5352_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec_ref(v_type_5283_);
v_a_5357_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5305_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5305_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
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
}
}
else
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
lean_dec_ref(v_type_5283_);
v_a_5366_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5295_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5295_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_);
lean_dec(v_a_5384_);
lean_dec_ref(v_a_5383_);
lean_dec(v_a_5382_);
lean_dec_ref(v_a_5381_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec_ref(v_a_5377_);
lean_dec(v_a_5376_);
lean_dec(v_a_5375_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_5387_, lean_object* v_x_5388_, lean_object* v_x_5389_){
_start:
{
lean_object* v___x_5390_; 
v___x_5390_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_5388_, v_x_5389_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5391_, lean_object* v_x_5392_, lean_object* v_x_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_5391_, v_x_5392_, v_x_5393_);
lean_dec_ref(v_x_5393_);
lean_dec_ref(v_x_5392_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5395_, lean_object* v_x_5396_, size_t v_x_5397_, lean_object* v_x_5398_){
_start:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5396_, v_x_5397_, v_x_5398_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5400_, lean_object* v_x_5401_, lean_object* v_x_5402_, lean_object* v_x_5403_){
_start:
{
size_t v_x_8306__boxed_5404_; lean_object* v_res_5405_; 
v_x_8306__boxed_5404_ = lean_unbox_usize(v_x_5402_);
lean_dec(v_x_5402_);
v_res_5405_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_5400_, v_x_5401_, v_x_8306__boxed_5404_, v_x_5403_);
lean_dec_ref(v_x_5403_);
lean_dec_ref(v_x_5401_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5406_, lean_object* v_keys_5407_, lean_object* v_vals_5408_, lean_object* v_heq_5409_, lean_object* v_i_5410_, lean_object* v_k_5411_){
_start:
{
lean_object* v___x_5412_; 
v___x_5412_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5407_, v_vals_5408_, v_i_5410_, v_k_5411_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5413_, lean_object* v_keys_5414_, lean_object* v_vals_5415_, lean_object* v_heq_5416_, lean_object* v_i_5417_, lean_object* v_k_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5413_, v_keys_5414_, v_vals_5415_, v_heq_5416_, v_i_5417_, v_k_5418_);
lean_dec_ref(v_k_5418_);
lean_dec_ref(v_vals_5415_);
lean_dec_ref(v_keys_5414_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_5420_, lean_object* v_type_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_){
_start:
{
lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_5429_ = lean_box(0);
v___x_5430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5430_, 0, v_u_5420_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = l_Lean_mkConst(v___x_5428_, v___x_5430_);
v___x_5432_ = l_Lean_Expr_app___override(v___x_5431_, v_type_5421_);
v___x_5433_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5432_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_5434_, lean_object* v_type_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_){
_start:
{
lean_object* v_res_5442_; 
v_res_5442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_5434_, v_type_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
lean_dec(v_a_5440_);
lean_dec_ref(v_a_5439_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
return v_res_5442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_5443_, lean_object* v_type_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_){
_start:
{
lean_object* v___x_5456_; 
v___x_5456_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_5443_, v_type_5444_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_5457_, lean_object* v_type_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_5457_, v_type_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
lean_dec(v_a_5468_);
lean_dec_ref(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec_ref(v_a_5465_);
lean_dec(v_a_5464_);
lean_dec_ref(v_a_5463_);
lean_dec(v_a_5462_);
lean_dec_ref(v_a_5461_);
lean_dec(v_a_5460_);
lean_dec(v_a_5459_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_5471_, lean_object* v_s_5472_){
_start:
{
lean_object* v_structs_5473_; lean_object* v_typeIdOf_5474_; lean_object* v_exprToStructId_5475_; lean_object* v_exprToStructIdEntries_5476_; lean_object* v_forbiddenNatModules_5477_; lean_object* v_natStructs_5478_; lean_object* v_natTypeIdOf_5479_; lean_object* v_exprToNatStructId_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5488_; 
v_structs_5473_ = lean_ctor_get(v_s_5472_, 0);
v_typeIdOf_5474_ = lean_ctor_get(v_s_5472_, 1);
v_exprToStructId_5475_ = lean_ctor_get(v_s_5472_, 2);
v_exprToStructIdEntries_5476_ = lean_ctor_get(v_s_5472_, 3);
v_forbiddenNatModules_5477_ = lean_ctor_get(v_s_5472_, 4);
v_natStructs_5478_ = lean_ctor_get(v_s_5472_, 5);
v_natTypeIdOf_5479_ = lean_ctor_get(v_s_5472_, 6);
v_exprToNatStructId_5480_ = lean_ctor_get(v_s_5472_, 7);
v_isSharedCheck_5488_ = !lean_is_exclusive(v_s_5472_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5482_ = v_s_5472_;
v_isShared_5483_ = v_isSharedCheck_5488_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_exprToNatStructId_5480_);
lean_inc(v_natTypeIdOf_5479_);
lean_inc(v_natStructs_5478_);
lean_inc(v_forbiddenNatModules_5477_);
lean_inc(v_exprToStructIdEntries_5476_);
lean_inc(v_exprToStructId_5475_);
lean_inc(v_typeIdOf_5474_);
lean_inc(v_structs_5473_);
lean_dec(v_s_5472_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5488_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_array_push(v_natStructs_5478_, v___x_5471_);
if (v_isShared_5483_ == 0)
{
lean_ctor_set(v___x_5482_, 5, v___x_5484_);
v___x_5486_ = v___x_5482_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_structs_5473_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v_typeIdOf_5474_);
lean_ctor_set(v_reuseFailAlloc_5487_, 2, v_exprToStructId_5475_);
lean_ctor_set(v_reuseFailAlloc_5487_, 3, v_exprToStructIdEntries_5476_);
lean_ctor_set(v_reuseFailAlloc_5487_, 4, v_forbiddenNatModules_5477_);
lean_ctor_set(v_reuseFailAlloc_5487_, 5, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5487_, 6, v_natTypeIdOf_5479_);
lean_ctor_set(v_reuseFailAlloc_5487_, 7, v_exprToNatStructId_5480_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v_ref_5495_; lean_object* v___x_5496_; lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5505_; 
v_ref_5495_ = lean_ctor_get(v___y_5492_, 5);
v___x_5496_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5499_ = v___x_5496_;
v_isShared_5500_ = v_isSharedCheck_5505_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5496_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5505_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5501_; lean_object* v___x_5503_; 
lean_inc(v_ref_5495_);
v___x_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5501_, 0, v_ref_5495_);
lean_ctor_set(v___x_5501_, 1, v_a_5497_);
if (v_isShared_5500_ == 0)
{
lean_ctor_set_tag(v___x_5499_, 1);
lean_ctor_set(v___x_5499_, 0, v___x_5501_);
v___x_5503_ = v___x_5499_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
return v_res_5512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4(void){
_start:
{
lean_object* v___x_5519_; 
v___x_5519_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
v___x_5520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4);
v___x_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5521_, 0, v___x_5520_);
return v___x_5521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
v___x_5524_ = l_Lean_stringToMessageData(v___x_5523_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v_orderedAddInst_x3f_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; lean_object* v___y_5706_; lean_object* v___y_5707_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___y_5723_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v_____do__lift_5740_; lean_object* v___y_5741_; lean_object* v___y_5742_; lean_object* v___y_5743_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5808_; lean_object* v___y_5809_; lean_object* v___y_5810_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v_____do__lift_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; lean_object* v___y_5857_; lean_object* v___y_5858_; lean_object* v___y_5859_; lean_object* v___y_5860_; lean_object* v___y_5861_; lean_object* v___y_5862_; lean_object* v___y_5863_; lean_object* v___y_5864_; lean_object* v_____do__lift_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; lean_object* v___y_5875_; lean_object* v___y_5899_; lean_object* v___y_5900_; lean_object* v___y_5901_; lean_object* v___y_5902_; lean_object* v___y_5903_; lean_object* v___y_5904_; lean_object* v___y_5905_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5908_; lean_object* v___y_5909_; lean_object* v_____do__lift_5910_; lean_object* v___y_5911_; lean_object* v___y_5912_; lean_object* v___y_5913_; lean_object* v___y_5914_; lean_object* v___y_5915_; lean_object* v___y_5916_; lean_object* v___y_5917_; lean_object* v___y_5918_; lean_object* v___y_5919_; lean_object* v___y_5920_; lean_object* v___y_5945_; lean_object* v___y_5946_; lean_object* v___y_5947_; lean_object* v___y_5948_; lean_object* v___y_5949_; lean_object* v___y_5950_; lean_object* v___y_5951_; lean_object* v___y_5952_; lean_object* v___y_5953_; lean_object* v___y_5954_; lean_object* v_____do__lift_5955_; lean_object* v___y_5956_; lean_object* v___y_5957_; lean_object* v___y_5958_; lean_object* v___y_5959_; lean_object* v___y_5960_; lean_object* v___y_5961_; lean_object* v___y_5962_; lean_object* v___y_5963_; lean_object* v___y_5964_; lean_object* v___y_5965_; lean_object* v_val_5990_; lean_object* v___x_6058_; 
v___x_6058_ = l_Lean_leCarrierIsSort(v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_a_6059_; uint8_t v___x_6060_; 
v_a_6059_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_a_6059_);
lean_dec_ref_known(v___x_6058_, 1);
v___x_6060_ = lean_unbox(v_a_6059_);
lean_dec(v_a_6059_);
if (v___x_6060_ == 0)
{
lean_object* v___x_6061_; 
lean_inc_ref(v_type_5525_);
v___x_6061_ = l_Lean_Meta_getDecLevel(v_type_5525_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6061_) == 0)
{
lean_object* v_a_6062_; 
v_a_6062_ = lean_ctor_get(v___x_6061_, 0);
lean_inc(v_a_6062_);
lean_dec_ref_known(v___x_6061_, 1);
v_val_5990_ = v_a_6062_;
goto v___jp_5989_;
}
else
{
lean_object* v_a_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6070_; 
lean_dec_ref(v_type_5525_);
v_a_6063_ = lean_ctor_get(v___x_6061_, 0);
v_isSharedCheck_6070_ = !lean_is_exclusive(v___x_6061_);
if (v_isSharedCheck_6070_ == 0)
{
v___x_6065_ = v___x_6061_;
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_a_6063_);
lean_dec(v___x_6061_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v___x_6068_; 
if (v_isShared_6066_ == 0)
{
v___x_6068_ = v___x_6065_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6069_; 
v_reuseFailAlloc_6069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_a_6063_);
v___x_6068_ = v_reuseFailAlloc_6069_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
return v___x_6068_;
}
}
}
}
else
{
lean_object* v___x_6071_; 
lean_inc_ref(v_type_5525_);
v___x_6071_ = l_Lean_Meta_getDecLevel_x3f(v_type_5525_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_object* v_a_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6081_; 
v_a_6072_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6074_ = v___x_6071_;
v_isShared_6075_ = v_isSharedCheck_6081_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_a_6072_);
lean_dec(v___x_6071_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6081_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
if (lean_obj_tag(v_a_6072_) == 1)
{
lean_object* v_val_6076_; 
lean_del_object(v___x_6074_);
v_val_6076_ = lean_ctor_get(v_a_6072_, 0);
lean_inc(v_val_6076_);
lean_dec_ref_known(v_a_6072_, 1);
v_val_5990_ = v_val_6076_;
goto v___jp_5989_;
}
else
{
lean_object* v___x_6077_; lean_object* v___x_6079_; 
lean_dec(v_a_6072_);
lean_dec_ref(v_type_5525_);
v___x_6077_ = lean_box(0);
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 0, v___x_6077_);
v___x_6079_ = v___x_6074_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v___x_6077_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
else
{
lean_object* v_a_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6089_; 
lean_dec_ref(v_type_5525_);
v_a_6082_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6089_ == 0)
{
v___x_6084_ = v___x_6071_;
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_a_6082_);
lean_dec(v___x_6071_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6087_; 
if (v_isShared_6085_ == 0)
{
v___x_6087_ = v___x_6084_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6082_);
v___x_6087_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
return v___x_6087_;
}
}
}
}
}
else
{
lean_object* v_a_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6097_; 
lean_dec_ref(v_type_5525_);
v_a_6090_ = lean_ctor_get(v___x_6058_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v___x_6058_);
if (v_isSharedCheck_6097_ == 0)
{
v___x_6092_ = v___x_6058_;
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_a_6090_);
lean_dec(v___x_6058_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6097_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6095_; 
if (v_isShared_6093_ == 0)
{
v___x_6095_ = v___x_6092_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_a_6090_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
return v___x_6095_;
}
}
}
v___jp_5537_:
{
lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
v___x_5566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13));
lean_inc(v___y_5544_);
v___x_5567_ = l_Lean_mkConst(v___x_5566_, v___y_5544_);
lean_inc_ref(v_type_5525_);
v___x_5568_ = l_Lean_Expr_app___override(v___x_5567_, v_type_5525_);
v___x_5569_ = l_Lean_Meta_Sym_synthInstance(v___x_5568_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5569_) == 0)
{
lean_object* v_a_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
lean_inc(v_a_5570_);
lean_dec_ref_known(v___x_5569_, 1);
v___x_5571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___y_5554_);
lean_inc_ref(v___y_5540_);
v___x_5572_ = l_Lean_Name_mkStr3(v___y_5540_, v___y_5554_, v___x_5571_);
lean_inc(v___y_5544_);
v___x_5573_ = l_Lean_mkConst(v___x_5572_, v___y_5544_);
lean_inc_ref(v_type_5525_);
v___x_5574_ = l_Lean_mkAppB(v___x_5573_, v_type_5525_, v_a_5570_);
v___x_5575_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5574_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5575_, 1);
v___x_5577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0));
lean_inc_ref(v___y_5546_);
lean_inc_ref(v___y_5547_);
lean_inc_ref(v___y_5554_);
lean_inc_ref(v___y_5540_);
v___x_5578_ = l_Lean_Name_mkStr5(v___y_5540_, v___y_5554_, v___y_5547_, v___y_5546_, v___x_5577_);
lean_inc(v___y_5544_);
v___x_5579_ = l_Lean_mkConst(v___x_5578_, v___y_5544_);
lean_inc_ref(v___y_5538_);
lean_inc_ref(v_type_5525_);
v___x_5580_ = l_Lean_mkAppB(v___x_5579_, v_type_5525_, v___y_5538_);
v___x_5581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5580_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; 
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v___x_5581_, 1);
v___x_5583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc_ref(v_type_5525_);
lean_inc(v___y_5553_);
v___x_5584_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_5583_, v___y_5553_, v_type_5525_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_a_5585_ = lean_ctor_get(v___x_5584_, 0);
lean_inc(v_a_5585_);
lean_dec_ref_known(v___x_5584_, 1);
v___x_5586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_5587_ = l_Lean_mkConst(v___x_5586_, v___y_5544_);
lean_inc_ref(v_type_5525_);
v___x_5588_ = l_Lean_mkAppB(v___x_5587_, v_type_5525_, v_a_5585_);
v___x_5589_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_5588_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5591_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_a_5590_);
lean_dec_ref_known(v___x_5589_, 1);
lean_inc_ref(v_type_5525_);
lean_inc(v___y_5553_);
v___x_5591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v___y_5553_, v_type_5525_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_a_5592_);
lean_dec_ref_known(v___x_5591_, 1);
v___x_5593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_5594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_5595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5594_);
lean_ctor_set(v___x_5595_, 1, v___y_5549_);
v___x_5596_ = l_Lean_mkConst(v___x_5593_, v___x_5595_);
v___x_5597_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_5525_, 2);
v___x_5598_ = l_Lean_mkApp4(v___x_5596_, v___x_5597_, v_type_5525_, v_type_5525_, v_a_5592_);
v___x_5599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5598_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_a_5600_; lean_object* v___x_5601_; 
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
lean_inc(v_a_5600_);
lean_dec_ref_known(v___x_5599_, 1);
v___x_5601_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_5556_, v___y_5564_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_a_5602_; lean_object* v_natStructs_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___f_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
lean_inc(v_a_5602_);
lean_dec_ref_known(v___x_5601_, 1);
v_natStructs_5603_ = lean_ctor_get(v_a_5602_, 5);
lean_inc_ref(v_natStructs_5603_);
lean_dec(v_a_5602_);
v___x_5604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3));
lean_inc(v___y_5553_);
v___x_5605_ = l_Lean_Level_succ___override(v___y_5553_);
lean_inc(v___y_5552_);
v___x_5606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5605_);
lean_ctor_set(v___x_5606_, 1, v___y_5552_);
v___x_5607_ = l_Lean_mkConst(v___x_5604_, v___x_5606_);
v___x_5608_ = l_Lean_Expr_app___override(v___x_5607_, v___y_5542_);
v___x_5609_ = lean_array_get_size(v_natStructs_5603_);
lean_dec_ref(v_natStructs_5603_);
v___x_5610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_5611_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5609_);
lean_ctor_set(v___x_5611_, 1, v___y_5541_);
lean_ctor_set(v___x_5611_, 2, v_type_5525_);
lean_ctor_set(v___x_5611_, 3, v___y_5553_);
lean_ctor_set(v___x_5611_, 4, v___y_5538_);
lean_ctor_set(v___x_5611_, 5, v___y_5539_);
lean_ctor_set(v___x_5611_, 6, v___y_5551_);
lean_ctor_set(v___x_5611_, 7, v___y_5548_);
lean_ctor_set(v___x_5611_, 8, v___y_5550_);
lean_ctor_set(v___x_5611_, 9, v_orderedAddInst_x3f_5555_);
lean_ctor_set(v___x_5611_, 10, v___y_5545_);
lean_ctor_set(v___x_5611_, 11, v_a_5576_);
lean_ctor_set(v___x_5611_, 12, v___x_5608_);
lean_ctor_set(v___x_5611_, 13, v_a_5590_);
lean_ctor_set(v___x_5611_, 14, v_a_5582_);
lean_ctor_set(v___x_5611_, 15, v___y_5543_);
lean_ctor_set(v___x_5611_, 16, v_a_5600_);
lean_ctor_set(v___x_5611_, 17, v___x_5610_);
v___f_5612_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_5612_, 0, v___x_5611_);
v___x_5613_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5614_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5613_, v___f_5612_, v___y_5556_);
if (lean_obj_tag(v___x_5614_) == 0)
{
lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5622_; 
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5614_);
if (v_isSharedCheck_5622_ == 0)
{
lean_object* v_unused_5623_; 
v_unused_5623_ = lean_ctor_get(v___x_5614_, 0);
lean_dec(v_unused_5623_);
v___x_5616_ = v___x_5614_;
v_isShared_5617_ = v_isSharedCheck_5622_;
goto v_resetjp_5615_;
}
else
{
lean_dec(v___x_5614_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5622_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5618_; lean_object* v___x_5620_; 
v___x_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5609_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 0, v___x_5618_);
v___x_5620_ = v___x_5616_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5618_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
v_a_5624_ = lean_ctor_get(v___x_5614_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5614_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5614_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5614_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5600_);
lean_dec(v_a_5590_);
lean_dec(v_a_5582_);
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5632_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5601_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5601_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec(v_a_5590_);
lean_dec(v_a_5582_);
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5640_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5599_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5599_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
else
{
lean_object* v_a_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5655_; 
lean_dec(v_a_5590_);
lean_dec(v_a_5582_);
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5648_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5655_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5650_ = v___x_5591_;
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_a_5648_);
lean_dec(v___x_5591_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5655_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5653_; 
if (v_isShared_5651_ == 0)
{
v___x_5653_ = v___x_5650_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_a_5648_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_dec(v_a_5582_);
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5656_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5589_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5589_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
lean_dec(v_a_5582_);
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5664_ = lean_ctor_get(v___x_5584_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5584_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5584_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
lean_dec(v_a_5576_);
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5672_ = lean_ctor_get(v___x_5581_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5581_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5581_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5581_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5680_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5575_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5575_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
else
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5695_; 
lean_dec(v_orderedAddInst_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v___y_5542_);
lean_dec(v___y_5541_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec_ref(v_type_5525_);
v_a_5688_ = lean_ctor_get(v___x_5569_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5690_ = v___x_5569_;
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v___x_5569_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
v___jp_5696_:
{
lean_object* v___x_5724_; 
v___x_5724_ = lean_box(0);
v___y_5538_ = v___y_5697_;
v___y_5539_ = v___y_5698_;
v___y_5540_ = v___y_5699_;
v___y_5541_ = v___y_5700_;
v___y_5542_ = v___y_5701_;
v___y_5543_ = v___y_5702_;
v___y_5544_ = v___y_5703_;
v___y_5545_ = v___y_5704_;
v___y_5546_ = v___y_5705_;
v___y_5547_ = v___y_5706_;
v___y_5548_ = v___y_5707_;
v___y_5549_ = v___y_5708_;
v___y_5550_ = v___y_5709_;
v___y_5551_ = v___y_5710_;
v___y_5552_ = v___y_5711_;
v___y_5553_ = v___y_5712_;
v___y_5554_ = v___y_5713_;
v_orderedAddInst_x3f_5555_ = v___x_5724_;
v___y_5556_ = v___y_5714_;
v___y_5557_ = v___y_5715_;
v___y_5558_ = v___y_5716_;
v___y_5559_ = v___y_5717_;
v___y_5560_ = v___y_5718_;
v___y_5561_ = v___y_5719_;
v___y_5562_ = v___y_5720_;
v___y_5563_ = v___y_5721_;
v___y_5564_ = v___y_5722_;
v___y_5565_ = v___y_5723_;
goto v___jp_5537_;
}
v___jp_5725_:
{
lean_object* v___x_5751_; 
lean_inc(v___y_5726_);
lean_inc_ref(v_type_5525_);
v___x_5751_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_____do__lift_5740_, v_type_5525_, v___y_5726_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
if (lean_obj_tag(v___x_5751_) == 0)
{
lean_object* v_a_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
v_a_5752_ = lean_ctor_get(v___x_5751_, 0);
lean_inc(v_a_5752_);
lean_dec_ref_known(v___x_5751_, 1);
v___x_5753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_type_5525_);
lean_inc(v___y_5738_);
v___x_5754_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_5753_, v___y_5738_, v_type_5525_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v_a_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
lean_inc_n(v_a_5755_, 2);
lean_dec_ref_known(v___x_5754_, 1);
v___x_5756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
lean_inc(v___y_5731_);
lean_inc_n(v___y_5738_, 2);
v___x_5757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___y_5738_);
lean_ctor_set(v___x_5757_, 1, v___y_5731_);
lean_inc_ref(v___x_5757_);
v___x_5758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___y_5738_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = l_Lean_mkConst(v___x_5756_, v___x_5758_);
lean_inc_ref_n(v_type_5525_, 3);
v___x_5760_ = l_Lean_mkApp4(v___x_5759_, v_type_5525_, v_type_5525_, v_type_5525_, v_a_5755_);
v___x_5761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5760_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
if (lean_obj_tag(v___x_5761_) == 0)
{
if (lean_obj_tag(v___y_5726_) == 1)
{
if (lean_obj_tag(v___y_5735_) == 1)
{
lean_object* v_a_5762_; lean_object* v_val_5763_; lean_object* v_val_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5762_);
lean_dec_ref_known(v___x_5761_, 1);
v_val_5763_ = lean_ctor_get(v___y_5726_, 0);
v_val_5764_ = lean_ctor_get(v___y_5735_, 0);
v___x_5765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59));
lean_inc_ref(v___y_5739_);
lean_inc_ref(v___y_5728_);
v___x_5766_ = l_Lean_Name_mkStr3(v___y_5728_, v___y_5739_, v___x_5765_);
lean_inc(v___y_5731_);
v___x_5767_ = l_Lean_mkConst(v___x_5766_, v___y_5731_);
lean_inc(v_val_5764_);
lean_inc(v_val_5763_);
lean_inc_ref(v_type_5525_);
v___x_5768_ = l_Lean_mkApp4(v___x_5767_, v_type_5525_, v_a_5755_, v_val_5763_, v_val_5764_);
v___x_5769_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5768_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_);
if (lean_obj_tag(v___x_5769_) == 0)
{
lean_object* v_a_5770_; 
v_a_5770_ = lean_ctor_get(v___x_5769_, 0);
lean_inc(v_a_5770_);
lean_dec_ref_known(v___x_5769_, 1);
v___y_5538_ = v___y_5727_;
v___y_5539_ = v___y_5726_;
v___y_5540_ = v___y_5728_;
v___y_5541_ = v___y_5729_;
v___y_5542_ = v___y_5730_;
v___y_5543_ = v_a_5762_;
v___y_5544_ = v___y_5731_;
v___y_5545_ = v_a_5752_;
v___y_5546_ = v___y_5732_;
v___y_5547_ = v___y_5733_;
v___y_5548_ = v___y_5734_;
v___y_5549_ = v___x_5757_;
v___y_5550_ = v___y_5735_;
v___y_5551_ = v___y_5736_;
v___y_5552_ = v___y_5737_;
v___y_5553_ = v___y_5738_;
v___y_5554_ = v___y_5739_;
v_orderedAddInst_x3f_5555_ = v_a_5770_;
v___y_5556_ = v___y_5741_;
v___y_5557_ = v___y_5742_;
v___y_5558_ = v___y_5743_;
v___y_5559_ = v___y_5744_;
v___y_5560_ = v___y_5745_;
v___y_5561_ = v___y_5746_;
v___y_5562_ = v___y_5747_;
v___y_5563_ = v___y_5748_;
v___y_5564_ = v___y_5749_;
v___y_5565_ = v___y_5750_;
goto v___jp_5537_;
}
else
{
lean_object* v_a_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5778_; 
lean_dec_ref_known(v___y_5735_, 1);
lean_dec(v_a_5762_);
lean_dec_ref_known(v___y_5726_, 1);
lean_dec_ref_known(v___x_5757_, 2);
lean_dec(v_a_5752_);
lean_dec(v___y_5738_);
lean_dec(v___y_5736_);
lean_dec(v___y_5734_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5727_);
lean_dec_ref(v_type_5525_);
v_a_5771_ = lean_ctor_get(v___x_5769_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5769_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5773_ = v___x_5769_;
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_a_5771_);
lean_dec(v___x_5769_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5774_ == 0)
{
v___x_5776_ = v___x_5773_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
else
{
lean_object* v_a_5779_; 
lean_dec(v_a_5755_);
v_a_5779_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5779_);
lean_dec_ref_known(v___x_5761_, 1);
v___y_5697_ = v___y_5727_;
v___y_5698_ = v___y_5726_;
v___y_5699_ = v___y_5728_;
v___y_5700_ = v___y_5729_;
v___y_5701_ = v___y_5730_;
v___y_5702_ = v_a_5779_;
v___y_5703_ = v___y_5731_;
v___y_5704_ = v_a_5752_;
v___y_5705_ = v___y_5732_;
v___y_5706_ = v___y_5733_;
v___y_5707_ = v___y_5734_;
v___y_5708_ = v___x_5757_;
v___y_5709_ = v___y_5735_;
v___y_5710_ = v___y_5736_;
v___y_5711_ = v___y_5737_;
v___y_5712_ = v___y_5738_;
v___y_5713_ = v___y_5739_;
v___y_5714_ = v___y_5741_;
v___y_5715_ = v___y_5742_;
v___y_5716_ = v___y_5743_;
v___y_5717_ = v___y_5744_;
v___y_5718_ = v___y_5745_;
v___y_5719_ = v___y_5746_;
v___y_5720_ = v___y_5747_;
v___y_5721_ = v___y_5748_;
v___y_5722_ = v___y_5749_;
v___y_5723_ = v___y_5750_;
goto v___jp_5696_;
}
}
else
{
lean_object* v_a_5780_; 
lean_dec(v_a_5755_);
v_a_5780_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5780_);
lean_dec_ref_known(v___x_5761_, 1);
v___y_5697_ = v___y_5727_;
v___y_5698_ = v___y_5726_;
v___y_5699_ = v___y_5728_;
v___y_5700_ = v___y_5729_;
v___y_5701_ = v___y_5730_;
v___y_5702_ = v_a_5780_;
v___y_5703_ = v___y_5731_;
v___y_5704_ = v_a_5752_;
v___y_5705_ = v___y_5732_;
v___y_5706_ = v___y_5733_;
v___y_5707_ = v___y_5734_;
v___y_5708_ = v___x_5757_;
v___y_5709_ = v___y_5735_;
v___y_5710_ = v___y_5736_;
v___y_5711_ = v___y_5737_;
v___y_5712_ = v___y_5738_;
v___y_5713_ = v___y_5739_;
v___y_5714_ = v___y_5741_;
v___y_5715_ = v___y_5742_;
v___y_5716_ = v___y_5743_;
v___y_5717_ = v___y_5744_;
v___y_5718_ = v___y_5745_;
v___y_5719_ = v___y_5746_;
v___y_5720_ = v___y_5747_;
v___y_5721_ = v___y_5748_;
v___y_5722_ = v___y_5749_;
v___y_5723_ = v___y_5750_;
goto v___jp_5696_;
}
}
else
{
lean_object* v_a_5781_; lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5788_; 
lean_dec_ref_known(v___x_5757_, 2);
lean_dec(v_a_5755_);
lean_dec(v_a_5752_);
lean_dec(v___y_5738_);
lean_dec(v___y_5736_);
lean_dec(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v_type_5525_);
v_a_5781_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5783_ = v___x_5761_;
v_isShared_5784_ = v_isSharedCheck_5788_;
goto v_resetjp_5782_;
}
else
{
lean_inc(v_a_5781_);
lean_dec(v___x_5761_);
v___x_5783_ = lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5788_;
goto v_resetjp_5782_;
}
v_resetjp_5782_:
{
lean_object* v___x_5786_; 
if (v_isShared_5784_ == 0)
{
v___x_5786_ = v___x_5783_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
v___x_5786_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
return v___x_5786_;
}
}
}
}
else
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5796_; 
lean_dec(v_a_5752_);
lean_dec(v___y_5738_);
lean_dec(v___y_5736_);
lean_dec(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v_type_5525_);
v_a_5789_ = lean_ctor_get(v___x_5754_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5754_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5791_ = v___x_5754_;
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5754_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5792_ == 0)
{
v___x_5794_ = v___x_5791_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
}
else
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
lean_dec(v___y_5738_);
lean_dec(v___y_5736_);
lean_dec(v___y_5735_);
lean_dec(v___y_5734_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v_type_5525_);
v_a_5797_ = lean_ctor_get(v___x_5751_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5751_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5751_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5751_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
v___jp_5805_:
{
lean_object* v___x_5830_; 
lean_inc(v___y_5806_);
lean_inc(v___y_5815_);
lean_inc_ref(v_type_5525_);
v___x_5830_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_____do__lift_5819_, v_type_5525_, v___y_5815_, v___y_5806_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
if (lean_obj_tag(v___x_5830_) == 0)
{
lean_object* v_a_5831_; lean_object* v___x_5832_; 
v_a_5831_ = lean_ctor_get(v___x_5830_, 0);
lean_inc(v_a_5831_);
lean_dec_ref_known(v___x_5830_, 1);
v___x_5832_ = l_Lean_leCarrierIsSort(v___y_5828_, v___y_5829_);
if (lean_obj_tag(v___x_5832_) == 0)
{
lean_object* v_a_5833_; uint8_t v___x_5834_; 
v_a_5833_ = lean_ctor_get(v___x_5832_, 0);
lean_inc(v_a_5833_);
lean_dec_ref_known(v___x_5832_, 1);
v___x_5834_ = lean_unbox(v_a_5833_);
lean_dec(v_a_5833_);
if (v___x_5834_ == 0)
{
lean_inc(v___y_5817_);
v___y_5726_ = v___y_5806_;
v___y_5727_ = v___y_5807_;
v___y_5728_ = v___y_5808_;
v___y_5729_ = v___y_5809_;
v___y_5730_ = v___y_5810_;
v___y_5731_ = v___y_5811_;
v___y_5732_ = v___y_5812_;
v___y_5733_ = v___y_5813_;
v___y_5734_ = v_a_5831_;
v___y_5735_ = v___y_5814_;
v___y_5736_ = v___y_5815_;
v___y_5737_ = v___y_5816_;
v___y_5738_ = v___y_5817_;
v___y_5739_ = v___y_5818_;
v_____do__lift_5740_ = v___y_5817_;
v___y_5741_ = v___y_5820_;
v___y_5742_ = v___y_5821_;
v___y_5743_ = v___y_5822_;
v___y_5744_ = v___y_5823_;
v___y_5745_ = v___y_5824_;
v___y_5746_ = v___y_5825_;
v___y_5747_ = v___y_5826_;
v___y_5748_ = v___y_5827_;
v___y_5749_ = v___y_5828_;
v___y_5750_ = v___y_5829_;
goto v___jp_5725_;
}
else
{
lean_object* v___x_5835_; 
lean_inc(v___y_5817_);
v___x_5835_ = l_Lean_Level_succ___override(v___y_5817_);
v___y_5726_ = v___y_5806_;
v___y_5727_ = v___y_5807_;
v___y_5728_ = v___y_5808_;
v___y_5729_ = v___y_5809_;
v___y_5730_ = v___y_5810_;
v___y_5731_ = v___y_5811_;
v___y_5732_ = v___y_5812_;
v___y_5733_ = v___y_5813_;
v___y_5734_ = v_a_5831_;
v___y_5735_ = v___y_5814_;
v___y_5736_ = v___y_5815_;
v___y_5737_ = v___y_5816_;
v___y_5738_ = v___y_5817_;
v___y_5739_ = v___y_5818_;
v_____do__lift_5740_ = v___x_5835_;
v___y_5741_ = v___y_5820_;
v___y_5742_ = v___y_5821_;
v___y_5743_ = v___y_5822_;
v___y_5744_ = v___y_5823_;
v___y_5745_ = v___y_5824_;
v___y_5746_ = v___y_5825_;
v___y_5747_ = v___y_5826_;
v___y_5748_ = v___y_5827_;
v___y_5749_ = v___y_5828_;
v___y_5750_ = v___y_5829_;
goto v___jp_5725_;
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec(v_a_5831_);
lean_dec(v___y_5817_);
lean_dec(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec_ref(v_type_5525_);
v_a_5836_ = lean_ctor_get(v___x_5832_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5832_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5832_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5832_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
else
{
lean_object* v_a_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5851_; 
lean_dec(v___y_5817_);
lean_dec(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec_ref(v_type_5525_);
v_a_5844_ = lean_ctor_get(v___x_5830_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5830_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5846_ = v___x_5830_;
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_a_5844_);
lean_dec(v___x_5830_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5849_; 
if (v_isShared_5847_ == 0)
{
v___x_5849_ = v___x_5846_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
v___jp_5852_:
{
lean_object* v___x_5876_; 
lean_inc(v___y_5854_);
lean_inc_ref(v_type_5525_);
v___x_5876_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_____do__lift_5865_, v_type_5525_, v___y_5854_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
if (lean_obj_tag(v___x_5876_) == 0)
{
lean_object* v_a_5877_; lean_object* v___x_5878_; 
v_a_5877_ = lean_ctor_get(v___x_5876_, 0);
lean_inc(v_a_5877_);
lean_dec_ref_known(v___x_5876_, 1);
v___x_5878_ = l_Lean_leCarrierIsSort(v___y_5874_, v___y_5875_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; uint8_t v___x_5880_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5879_);
lean_dec_ref_known(v___x_5878_, 1);
v___x_5880_ = lean_unbox(v_a_5879_);
lean_dec(v_a_5879_);
if (v___x_5880_ == 0)
{
lean_inc(v___y_5861_);
v___y_5806_ = v___y_5854_;
v___y_5807_ = v___y_5853_;
v___y_5808_ = v___y_5855_;
v___y_5809_ = v___y_5856_;
v___y_5810_ = v___y_5857_;
v___y_5811_ = v___y_5858_;
v___y_5812_ = v___y_5862_;
v___y_5813_ = v___y_5864_;
v___y_5814_ = v_a_5877_;
v___y_5815_ = v___y_5859_;
v___y_5816_ = v___y_5860_;
v___y_5817_ = v___y_5861_;
v___y_5818_ = v___y_5863_;
v_____do__lift_5819_ = v___y_5861_;
v___y_5820_ = v___y_5866_;
v___y_5821_ = v___y_5867_;
v___y_5822_ = v___y_5868_;
v___y_5823_ = v___y_5869_;
v___y_5824_ = v___y_5870_;
v___y_5825_ = v___y_5871_;
v___y_5826_ = v___y_5872_;
v___y_5827_ = v___y_5873_;
v___y_5828_ = v___y_5874_;
v___y_5829_ = v___y_5875_;
goto v___jp_5805_;
}
else
{
lean_object* v___x_5881_; 
lean_inc(v___y_5861_);
v___x_5881_ = l_Lean_Level_succ___override(v___y_5861_);
v___y_5806_ = v___y_5854_;
v___y_5807_ = v___y_5853_;
v___y_5808_ = v___y_5855_;
v___y_5809_ = v___y_5856_;
v___y_5810_ = v___y_5857_;
v___y_5811_ = v___y_5858_;
v___y_5812_ = v___y_5862_;
v___y_5813_ = v___y_5864_;
v___y_5814_ = v_a_5877_;
v___y_5815_ = v___y_5859_;
v___y_5816_ = v___y_5860_;
v___y_5817_ = v___y_5861_;
v___y_5818_ = v___y_5863_;
v_____do__lift_5819_ = v___x_5881_;
v___y_5820_ = v___y_5866_;
v___y_5821_ = v___y_5867_;
v___y_5822_ = v___y_5868_;
v___y_5823_ = v___y_5869_;
v___y_5824_ = v___y_5870_;
v___y_5825_ = v___y_5871_;
v___y_5826_ = v___y_5872_;
v___y_5827_ = v___y_5873_;
v___y_5828_ = v___y_5874_;
v___y_5829_ = v___y_5875_;
goto v___jp_5805_;
}
}
else
{
lean_object* v_a_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5889_; 
lean_dec(v_a_5877_);
lean_dec(v___y_5861_);
lean_dec(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec_ref(v_type_5525_);
v_a_5882_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5884_ = v___x_5878_;
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_a_5882_);
lean_dec(v___x_5878_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
lean_object* v___x_5887_; 
if (v_isShared_5885_ == 0)
{
v___x_5887_ = v___x_5884_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
v___x_5887_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
return v___x_5887_;
}
}
}
}
else
{
lean_object* v_a_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5897_; 
lean_dec(v___y_5861_);
lean_dec(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec_ref(v_type_5525_);
v_a_5890_ = lean_ctor_get(v___x_5876_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v___x_5876_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5892_ = v___x_5876_;
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_a_5890_);
lean_dec(v___x_5876_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v___x_5895_; 
if (v_isShared_5893_ == 0)
{
v___x_5895_ = v___x_5892_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
}
v___jp_5898_:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_5525_);
v___x_5922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5921_, v_____do__lift_5910_, v_type_5525_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
if (lean_obj_tag(v___x_5922_) == 0)
{
lean_object* v_a_5923_; lean_object* v___x_5924_; 
v_a_5923_ = lean_ctor_get(v___x_5922_, 0);
lean_inc(v_a_5923_);
lean_dec_ref_known(v___x_5922_, 1);
v___x_5924_ = l_Lean_leCarrierIsSort(v___y_5919_, v___y_5920_);
if (lean_obj_tag(v___x_5924_) == 0)
{
lean_object* v_a_5925_; uint8_t v___x_5926_; 
v_a_5925_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_a_5925_);
lean_dec_ref_known(v___x_5924_, 1);
v___x_5926_ = lean_unbox(v_a_5925_);
lean_dec(v_a_5925_);
if (v___x_5926_ == 0)
{
lean_inc(v___y_5907_);
v___y_5853_ = v___y_5900_;
v___y_5854_ = v___y_5899_;
v___y_5855_ = v___y_5901_;
v___y_5856_ = v___y_5902_;
v___y_5857_ = v___y_5903_;
v___y_5858_ = v___y_5904_;
v___y_5859_ = v_a_5923_;
v___y_5860_ = v___y_5905_;
v___y_5861_ = v___y_5907_;
v___y_5862_ = v___y_5906_;
v___y_5863_ = v___y_5909_;
v___y_5864_ = v___y_5908_;
v_____do__lift_5865_ = v___y_5907_;
v___y_5866_ = v___y_5911_;
v___y_5867_ = v___y_5912_;
v___y_5868_ = v___y_5913_;
v___y_5869_ = v___y_5914_;
v___y_5870_ = v___y_5915_;
v___y_5871_ = v___y_5916_;
v___y_5872_ = v___y_5917_;
v___y_5873_ = v___y_5918_;
v___y_5874_ = v___y_5919_;
v___y_5875_ = v___y_5920_;
goto v___jp_5852_;
}
else
{
lean_object* v___x_5927_; 
lean_inc(v___y_5907_);
v___x_5927_ = l_Lean_Level_succ___override(v___y_5907_);
v___y_5853_ = v___y_5900_;
v___y_5854_ = v___y_5899_;
v___y_5855_ = v___y_5901_;
v___y_5856_ = v___y_5902_;
v___y_5857_ = v___y_5903_;
v___y_5858_ = v___y_5904_;
v___y_5859_ = v_a_5923_;
v___y_5860_ = v___y_5905_;
v___y_5861_ = v___y_5907_;
v___y_5862_ = v___y_5906_;
v___y_5863_ = v___y_5909_;
v___y_5864_ = v___y_5908_;
v_____do__lift_5865_ = v___x_5927_;
v___y_5866_ = v___y_5911_;
v___y_5867_ = v___y_5912_;
v___y_5868_ = v___y_5913_;
v___y_5869_ = v___y_5914_;
v___y_5870_ = v___y_5915_;
v___y_5871_ = v___y_5916_;
v___y_5872_ = v___y_5917_;
v___y_5873_ = v___y_5918_;
v___y_5874_ = v___y_5919_;
v___y_5875_ = v___y_5920_;
goto v___jp_5852_;
}
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5935_; 
lean_dec(v_a_5923_);
lean_dec(v___y_5907_);
lean_dec(v___y_5904_);
lean_dec_ref(v___y_5903_);
lean_dec(v___y_5902_);
lean_dec_ref(v___y_5900_);
lean_dec(v___y_5899_);
lean_dec_ref(v_type_5525_);
v_a_5928_ = lean_ctor_get(v___x_5924_, 0);
v_isSharedCheck_5935_ = !lean_is_exclusive(v___x_5924_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5930_ = v___x_5924_;
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5924_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
}
else
{
lean_object* v_a_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5943_; 
lean_dec(v___y_5907_);
lean_dec(v___y_5904_);
lean_dec_ref(v___y_5903_);
lean_dec(v___y_5902_);
lean_dec_ref(v___y_5900_);
lean_dec(v___y_5899_);
lean_dec_ref(v_type_5525_);
v_a_5936_ = lean_ctor_get(v___x_5922_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5922_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5938_ = v___x_5922_;
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_a_5936_);
lean_dec(v___x_5922_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5941_; 
if (v_isShared_5939_ == 0)
{
v___x_5941_ = v___x_5938_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5936_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
}
v___jp_5944_:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_type_5525_);
v___x_5967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5966_, v_____do__lift_5955_, v_type_5525_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_);
if (lean_obj_tag(v___x_5967_) == 0)
{
lean_object* v_a_5968_; lean_object* v___x_5969_; 
v_a_5968_ = lean_ctor_get(v___x_5967_, 0);
lean_inc(v_a_5968_);
lean_dec_ref_known(v___x_5967_, 1);
v___x_5969_ = l_Lean_leCarrierIsSort(v___y_5964_, v___y_5965_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_a_5970_; uint8_t v___x_5971_; 
v_a_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5970_);
lean_dec_ref_known(v___x_5969_, 1);
v___x_5971_ = lean_unbox(v_a_5970_);
lean_dec(v_a_5970_);
if (v___x_5971_ == 0)
{
lean_inc(v___y_5951_);
v___y_5899_ = v_a_5968_;
v___y_5900_ = v___y_5945_;
v___y_5901_ = v___y_5946_;
v___y_5902_ = v___y_5947_;
v___y_5903_ = v___y_5948_;
v___y_5904_ = v___y_5949_;
v___y_5905_ = v___y_5950_;
v___y_5906_ = v___y_5952_;
v___y_5907_ = v___y_5951_;
v___y_5908_ = v___y_5954_;
v___y_5909_ = v___y_5953_;
v_____do__lift_5910_ = v___y_5951_;
v___y_5911_ = v___y_5956_;
v___y_5912_ = v___y_5957_;
v___y_5913_ = v___y_5958_;
v___y_5914_ = v___y_5959_;
v___y_5915_ = v___y_5960_;
v___y_5916_ = v___y_5961_;
v___y_5917_ = v___y_5962_;
v___y_5918_ = v___y_5963_;
v___y_5919_ = v___y_5964_;
v___y_5920_ = v___y_5965_;
goto v___jp_5898_;
}
else
{
lean_object* v___x_5972_; 
lean_inc(v___y_5951_);
v___x_5972_ = l_Lean_Level_succ___override(v___y_5951_);
v___y_5899_ = v_a_5968_;
v___y_5900_ = v___y_5945_;
v___y_5901_ = v___y_5946_;
v___y_5902_ = v___y_5947_;
v___y_5903_ = v___y_5948_;
v___y_5904_ = v___y_5949_;
v___y_5905_ = v___y_5950_;
v___y_5906_ = v___y_5952_;
v___y_5907_ = v___y_5951_;
v___y_5908_ = v___y_5954_;
v___y_5909_ = v___y_5953_;
v_____do__lift_5910_ = v___x_5972_;
v___y_5911_ = v___y_5956_;
v___y_5912_ = v___y_5957_;
v___y_5913_ = v___y_5958_;
v___y_5914_ = v___y_5959_;
v___y_5915_ = v___y_5960_;
v___y_5916_ = v___y_5961_;
v___y_5917_ = v___y_5962_;
v___y_5918_ = v___y_5963_;
v___y_5919_ = v___y_5964_;
v___y_5920_ = v___y_5965_;
goto v___jp_5898_;
}
}
else
{
lean_object* v_a_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5980_; 
lean_dec(v_a_5968_);
lean_dec(v___y_5951_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec_ref(v___y_5945_);
lean_dec_ref(v_type_5525_);
v_a_5973_ = lean_ctor_get(v___x_5969_, 0);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_5980_ == 0)
{
v___x_5975_ = v___x_5969_;
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_a_5973_);
lean_dec(v___x_5969_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5978_; 
if (v_isShared_5976_ == 0)
{
v___x_5978_ = v___x_5975_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_a_5973_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
}
}
else
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_5988_; 
lean_dec(v___y_5951_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec_ref(v___y_5945_);
lean_dec_ref(v_type_5525_);
v_a_5981_ = lean_ctor_get(v___x_5967_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___x_5967_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5983_ = v___x_5967_;
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___x_5967_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5986_; 
if (v_isShared_5984_ == 0)
{
v___x_5986_ = v___x_5983_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5981_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
}
}
}
}
v___jp_5989_:
{
lean_object* v___x_5991_; 
lean_inc_ref(v_type_5525_);
lean_inc(v_val_5990_);
v___x_5991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_val_5990_, v_type_5525_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_5991_) == 0)
{
lean_object* v_a_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_6049_; 
v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_5994_ = v___x_5991_;
v_isShared_5995_ = v_isSharedCheck_6049_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_a_5992_);
lean_dec(v___x_5991_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_6049_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
if (lean_obj_tag(v_a_5992_) == 1)
{
lean_object* v_val_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; 
lean_del_object(v___x_5994_);
v_val_5996_ = lean_ctor_get(v_a_5992_, 0);
lean_inc_n(v_val_5996_, 2);
lean_dec_ref_known(v_a_5992_, 1);
v___x_5997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_5998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_5999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_6000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1));
v___x_6001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_6002_ = lean_box(0);
lean_inc(v_val_5990_);
v___x_6003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6003_, 0, v_val_5990_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
lean_inc_ref(v___x_6003_);
v___x_6004_ = l_Lean_mkConst(v___x_6001_, v___x_6003_);
lean_inc_ref(v_type_5525_);
v___x_6005_ = l_Lean_mkAppB(v___x_6004_, v_type_5525_, v_val_5996_);
v___x_6006_ = l_Lean_Meta_Sym_canon(v___x_6005_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6006_) == 0)
{
lean_object* v_a_6007_; lean_object* v___x_6008_; 
v_a_6007_ = lean_ctor_get(v___x_6006_, 0);
lean_inc(v_a_6007_);
lean_dec_ref_known(v___x_6006_, 1);
v___x_6008_ = l_Lean_Meta_Sym_shareCommon(v_a_6007_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6008_) == 0)
{
lean_object* v_a_6009_; lean_object* v___x_6010_; 
v_a_6009_ = lean_ctor_get(v___x_6008_, 0);
lean_inc_n(v_a_6009_, 2);
lean_dec_ref_known(v___x_6008_, 1);
v___x_6010_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_6009_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6010_) == 0)
{
lean_object* v_a_6011_; 
v_a_6011_ = lean_ctor_get(v___x_6010_, 0);
lean_inc(v_a_6011_);
lean_dec_ref_known(v___x_6010_, 1);
if (lean_obj_tag(v_a_6011_) == 1)
{
lean_object* v_val_6012_; lean_object* v___x_6013_; 
v_val_6012_ = lean_ctor_get(v_a_6011_, 0);
lean_inc(v_val_6012_);
lean_dec_ref_known(v_a_6011_, 1);
v___x_6013_ = l_Lean_leCarrierIsSort(v_a_5534_, v_a_5535_);
if (lean_obj_tag(v___x_6013_) == 0)
{
lean_object* v_a_6014_; uint8_t v___x_6015_; 
v_a_6014_ = lean_ctor_get(v___x_6013_, 0);
lean_inc(v_a_6014_);
lean_dec_ref_known(v___x_6013_, 1);
v___x_6015_ = lean_unbox(v_a_6014_);
lean_dec(v_a_6014_);
if (v___x_6015_ == 0)
{
lean_inc(v_val_5990_);
v___y_5945_ = v_val_5996_;
v___y_5946_ = v___x_5997_;
v___y_5947_ = v_val_6012_;
v___y_5948_ = v_a_6009_;
v___y_5949_ = v___x_6003_;
v___y_5950_ = v___x_6002_;
v___y_5951_ = v_val_5990_;
v___y_5952_ = v___x_6000_;
v___y_5953_ = v___x_5998_;
v___y_5954_ = v___x_5999_;
v_____do__lift_5955_ = v_val_5990_;
v___y_5956_ = v_a_5526_;
v___y_5957_ = v_a_5527_;
v___y_5958_ = v_a_5528_;
v___y_5959_ = v_a_5529_;
v___y_5960_ = v_a_5530_;
v___y_5961_ = v_a_5531_;
v___y_5962_ = v_a_5532_;
v___y_5963_ = v_a_5533_;
v___y_5964_ = v_a_5534_;
v___y_5965_ = v_a_5535_;
goto v___jp_5944_;
}
else
{
lean_object* v___x_6016_; 
lean_inc(v_val_5990_);
v___x_6016_ = l_Lean_Level_succ___override(v_val_5990_);
v___y_5945_ = v_val_5996_;
v___y_5946_ = v___x_5997_;
v___y_5947_ = v_val_6012_;
v___y_5948_ = v_a_6009_;
v___y_5949_ = v___x_6003_;
v___y_5950_ = v___x_6002_;
v___y_5951_ = v_val_5990_;
v___y_5952_ = v___x_6000_;
v___y_5953_ = v___x_5998_;
v___y_5954_ = v___x_5999_;
v_____do__lift_5955_ = v___x_6016_;
v___y_5956_ = v_a_5526_;
v___y_5957_ = v_a_5527_;
v___y_5958_ = v_a_5528_;
v___y_5959_ = v_a_5529_;
v___y_5960_ = v_a_5530_;
v___y_5961_ = v_a_5531_;
v___y_5962_ = v_a_5532_;
v___y_5963_ = v_a_5533_;
v___y_5964_ = v_a_5534_;
v___y_5965_ = v_a_5535_;
goto v___jp_5944_;
}
}
else
{
lean_object* v_a_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6024_; 
lean_dec(v_val_6012_);
lean_dec(v_a_6009_);
lean_dec_ref_known(v___x_6003_, 2);
lean_dec(v_val_5996_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v_a_6017_ = lean_ctor_get(v___x_6013_, 0);
v_isSharedCheck_6024_ = !lean_is_exclusive(v___x_6013_);
if (v_isSharedCheck_6024_ == 0)
{
v___x_6019_ = v___x_6013_;
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_a_6017_);
lean_dec(v___x_6013_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___x_6022_; 
if (v_isShared_6020_ == 0)
{
v___x_6022_ = v___x_6019_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6017_);
v___x_6022_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
return v___x_6022_;
}
}
}
}
else
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
lean_dec(v_a_6011_);
lean_dec_ref_known(v___x_6003_, 2);
lean_dec(v_val_5996_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v___x_6025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7);
v___x_6026_ = l_Lean_indentExpr(v_a_6009_);
v___x_6027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6027_, 0, v___x_6025_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v___x_6028_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_6027_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_6028_;
}
}
else
{
lean_dec(v_a_6009_);
lean_dec_ref_known(v___x_6003_, 2);
lean_dec(v_val_5996_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
return v___x_6010_;
}
}
else
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6036_; 
lean_dec_ref_known(v___x_6003_, 2);
lean_dec(v_val_5996_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v_a_6029_ = lean_ctor_get(v___x_6008_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v___x_6008_);
if (v_isSharedCheck_6036_ == 0)
{
v___x_6031_ = v___x_6008_;
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6008_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6034_; 
if (v_isShared_6032_ == 0)
{
v___x_6034_ = v___x_6031_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_a_6029_);
v___x_6034_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
return v___x_6034_;
}
}
}
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6044_; 
lean_dec_ref_known(v___x_6003_, 2);
lean_dec(v_val_5996_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v_a_6037_ = lean_ctor_get(v___x_6006_, 0);
v_isSharedCheck_6044_ = !lean_is_exclusive(v___x_6006_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6039_ = v___x_6006_;
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_a_6037_);
lean_dec(v___x_6006_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v___x_6042_; 
if (v_isShared_6040_ == 0)
{
v___x_6042_ = v___x_6039_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
else
{
lean_object* v___x_6045_; lean_object* v___x_6047_; 
lean_dec(v_a_5992_);
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v___x_6045_ = lean_box(0);
if (v_isShared_5995_ == 0)
{
lean_ctor_set(v___x_5994_, 0, v___x_6045_);
v___x_6047_ = v___x_5994_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6045_);
v___x_6047_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
return v___x_6047_;
}
}
}
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_dec(v_val_5990_);
lean_dec_ref(v_type_5525_);
v_a_6050_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_5991_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_5991_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_){
_start:
{
lean_object* v_res_6110_; 
v_res_6110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_6098_, v_a_6099_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_, v_a_6107_, v_a_6108_);
lean_dec(v_a_6108_);
lean_dec_ref(v_a_6107_);
lean_dec(v_a_6106_);
lean_dec_ref(v_a_6105_);
lean_dec(v_a_6104_);
lean_dec_ref(v_a_6103_);
lean_dec(v_a_6102_);
lean_dec_ref(v_a_6101_);
lean_dec(v_a_6100_);
lean_dec(v_a_6099_);
return v_res_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_6111_, lean_object* v_msg_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_6112_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_6125_, lean_object* v_msg_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_){
_start:
{
lean_object* v_res_6138_; 
v_res_6138_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_6125_, v_msg_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v___y_6134_);
lean_dec_ref(v___y_6133_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec(v___y_6127_);
return v_res_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_6139_, lean_object* v_a_6140_, lean_object* v_s_6141_){
_start:
{
lean_object* v_structs_6142_; lean_object* v_typeIdOf_6143_; lean_object* v_exprToStructId_6144_; lean_object* v_exprToStructIdEntries_6145_; lean_object* v_forbiddenNatModules_6146_; lean_object* v_natStructs_6147_; lean_object* v_natTypeIdOf_6148_; lean_object* v_exprToNatStructId_6149_; lean_object* v___x_6151_; uint8_t v_isShared_6152_; uint8_t v_isSharedCheck_6157_; 
v_structs_6142_ = lean_ctor_get(v_s_6141_, 0);
v_typeIdOf_6143_ = lean_ctor_get(v_s_6141_, 1);
v_exprToStructId_6144_ = lean_ctor_get(v_s_6141_, 2);
v_exprToStructIdEntries_6145_ = lean_ctor_get(v_s_6141_, 3);
v_forbiddenNatModules_6146_ = lean_ctor_get(v_s_6141_, 4);
v_natStructs_6147_ = lean_ctor_get(v_s_6141_, 5);
v_natTypeIdOf_6148_ = lean_ctor_get(v_s_6141_, 6);
v_exprToNatStructId_6149_ = lean_ctor_get(v_s_6141_, 7);
v_isSharedCheck_6157_ = !lean_is_exclusive(v_s_6141_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6151_ = v_s_6141_;
v_isShared_6152_ = v_isSharedCheck_6157_;
goto v_resetjp_6150_;
}
else
{
lean_inc(v_exprToNatStructId_6149_);
lean_inc(v_natTypeIdOf_6148_);
lean_inc(v_natStructs_6147_);
lean_inc(v_forbiddenNatModules_6146_);
lean_inc(v_exprToStructIdEntries_6145_);
lean_inc(v_exprToStructId_6144_);
lean_inc(v_typeIdOf_6143_);
lean_inc(v_structs_6142_);
lean_dec(v_s_6141_);
v___x_6151_ = lean_box(0);
v_isShared_6152_ = v_isSharedCheck_6157_;
goto v_resetjp_6150_;
}
v_resetjp_6150_:
{
lean_object* v___x_6153_; lean_object* v___x_6155_; 
v___x_6153_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_6148_, v_type_6139_, v_a_6140_);
if (v_isShared_6152_ == 0)
{
lean_ctor_set(v___x_6151_, 6, v___x_6153_);
v___x_6155_ = v___x_6151_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_structs_6142_);
lean_ctor_set(v_reuseFailAlloc_6156_, 1, v_typeIdOf_6143_);
lean_ctor_set(v_reuseFailAlloc_6156_, 2, v_exprToStructId_6144_);
lean_ctor_set(v_reuseFailAlloc_6156_, 3, v_exprToStructIdEntries_6145_);
lean_ctor_set(v_reuseFailAlloc_6156_, 4, v_forbiddenNatModules_6146_);
lean_ctor_set(v_reuseFailAlloc_6156_, 5, v_natStructs_6147_);
lean_ctor_set(v_reuseFailAlloc_6156_, 6, v___x_6153_);
lean_ctor_set(v_reuseFailAlloc_6156_, 7, v_exprToNatStructId_6149_);
v___x_6155_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
return v___x_6155_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_6158_, lean_object* v_i_6159_, lean_object* v_k_6160_){
_start:
{
lean_object* v___x_6161_; uint8_t v___x_6162_; 
v___x_6161_ = lean_array_get_size(v_keys_6158_);
v___x_6162_ = lean_nat_dec_lt(v_i_6159_, v___x_6161_);
if (v___x_6162_ == 0)
{
lean_dec(v_i_6159_);
return v___x_6162_;
}
else
{
lean_object* v_k_x27_6163_; size_t v___x_6164_; size_t v___x_6165_; uint8_t v___x_6166_; 
v_k_x27_6163_ = lean_array_fget_borrowed(v_keys_6158_, v_i_6159_);
v___x_6164_ = lean_ptr_addr(v_k_6160_);
v___x_6165_ = lean_ptr_addr(v_k_x27_6163_);
v___x_6166_ = lean_usize_dec_eq(v___x_6164_, v___x_6165_);
if (v___x_6166_ == 0)
{
lean_object* v___x_6167_; lean_object* v___x_6168_; 
v___x_6167_ = lean_unsigned_to_nat(1u);
v___x_6168_ = lean_nat_add(v_i_6159_, v___x_6167_);
lean_dec(v_i_6159_);
v_i_6159_ = v___x_6168_;
goto _start;
}
else
{
lean_dec(v_i_6159_);
return v___x_6166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_6170_, lean_object* v_i_6171_, lean_object* v_k_6172_){
_start:
{
uint8_t v_res_6173_; lean_object* v_r_6174_; 
v_res_6173_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_6170_, v_i_6171_, v_k_6172_);
lean_dec_ref(v_k_6172_);
lean_dec_ref(v_keys_6170_);
v_r_6174_ = lean_box(v_res_6173_);
return v_r_6174_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_6175_, size_t v_x_6176_, lean_object* v_x_6177_){
_start:
{
if (lean_obj_tag(v_x_6175_) == 0)
{
lean_object* v_es_6178_; lean_object* v___x_6179_; size_t v___x_6180_; size_t v___x_6181_; lean_object* v_j_6182_; lean_object* v___x_6183_; 
v_es_6178_ = lean_ctor_get(v_x_6175_, 0);
v___x_6179_ = lean_box(2);
v___x_6180_ = ((size_t)31ULL);
v___x_6181_ = lean_usize_land(v_x_6176_, v___x_6180_);
v_j_6182_ = lean_usize_to_nat(v___x_6181_);
v___x_6183_ = lean_array_get_borrowed(v___x_6179_, v_es_6178_, v_j_6182_);
lean_dec(v_j_6182_);
switch(lean_obj_tag(v___x_6183_))
{
case 0:
{
lean_object* v_key_6184_; size_t v___x_6185_; size_t v___x_6186_; uint8_t v___x_6187_; 
v_key_6184_ = lean_ctor_get(v___x_6183_, 0);
v___x_6185_ = lean_ptr_addr(v_x_6177_);
v___x_6186_ = lean_ptr_addr(v_key_6184_);
v___x_6187_ = lean_usize_dec_eq(v___x_6185_, v___x_6186_);
return v___x_6187_;
}
case 1:
{
lean_object* v_node_6188_; size_t v___x_6189_; size_t v___x_6190_; 
v_node_6188_ = lean_ctor_get(v___x_6183_, 0);
v___x_6189_ = ((size_t)5ULL);
v___x_6190_ = lean_usize_shift_right(v_x_6176_, v___x_6189_);
v_x_6175_ = v_node_6188_;
v_x_6176_ = v___x_6190_;
goto _start;
}
default: 
{
uint8_t v___x_6192_; 
v___x_6192_ = 0;
return v___x_6192_;
}
}
}
else
{
lean_object* v_ks_6193_; lean_object* v___x_6194_; uint8_t v___x_6195_; 
v_ks_6193_ = lean_ctor_get(v_x_6175_, 0);
v___x_6194_ = lean_unsigned_to_nat(0u);
v___x_6195_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_6193_, v___x_6194_, v_x_6177_);
return v___x_6195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_6196_, lean_object* v_x_6197_, lean_object* v_x_6198_){
_start:
{
size_t v_x_10663__boxed_6199_; uint8_t v_res_6200_; lean_object* v_r_6201_; 
v_x_10663__boxed_6199_ = lean_unbox_usize(v_x_6197_);
lean_dec(v_x_6197_);
v_res_6200_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6196_, v_x_10663__boxed_6199_, v_x_6198_);
lean_dec_ref(v_x_6198_);
lean_dec_ref(v_x_6196_);
v_r_6201_ = lean_box(v_res_6200_);
return v_r_6201_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_6202_, lean_object* v_x_6203_){
_start:
{
size_t v___x_6204_; size_t v___x_6205_; size_t v___x_6206_; uint64_t v___x_6207_; size_t v___x_6208_; uint8_t v___x_6209_; 
v___x_6204_ = lean_ptr_addr(v_x_6203_);
v___x_6205_ = ((size_t)3ULL);
v___x_6206_ = lean_usize_shift_right(v___x_6204_, v___x_6205_);
v___x_6207_ = lean_usize_to_uint64(v___x_6206_);
v___x_6208_ = lean_uint64_to_usize(v___x_6207_);
v___x_6209_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6202_, v___x_6208_, v_x_6203_);
return v___x_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_6210_, lean_object* v_x_6211_){
_start:
{
uint8_t v_res_6212_; lean_object* v_r_6213_; 
v_res_6212_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_6210_, v_x_6211_);
lean_dec_ref(v_x_6211_);
lean_dec_ref(v_x_6210_);
v_r_6213_ = lean_box(v_res_6212_);
return v_r_6213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_6214_, lean_object* v_a_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_6217_);
if (lean_obj_tag(v___x_6226_) == 0)
{
lean_object* v_a_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6316_; 
v_a_6227_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6316_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6316_ == 0)
{
v___x_6229_ = v___x_6226_;
v_isShared_6230_ = v_isSharedCheck_6316_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_a_6227_);
lean_dec(v___x_6226_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6316_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
uint8_t v_linarith_6231_; 
v_linarith_6231_ = lean_ctor_get_uint8(v_a_6227_, sizeof(void*)*14 + 22);
lean_dec(v_a_6227_);
if (v_linarith_6231_ == 0)
{
lean_object* v___x_6232_; lean_object* v___x_6234_; 
lean_dec_ref(v_type_6214_);
v___x_6232_ = lean_box(0);
if (v_isShared_6230_ == 0)
{
lean_ctor_set(v___x_6229_, 0, v___x_6232_);
v___x_6234_ = v___x_6229_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6235_; 
v_reuseFailAlloc_6235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6235_, 0, v___x_6232_);
v___x_6234_ = v_reuseFailAlloc_6235_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
return v___x_6234_;
}
}
else
{
lean_object* v___x_6236_; 
lean_del_object(v___x_6229_);
v___x_6236_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6215_, v_a_6223_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v_a_6237_; lean_object* v___x_6239_; uint8_t v_isShared_6240_; uint8_t v_isSharedCheck_6307_; 
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6239_ = v___x_6236_;
v_isShared_6240_ = v_isSharedCheck_6307_;
goto v_resetjp_6238_;
}
else
{
lean_inc(v_a_6237_);
lean_dec(v___x_6236_);
v___x_6239_ = lean_box(0);
v_isShared_6240_ = v_isSharedCheck_6307_;
goto v_resetjp_6238_;
}
v_resetjp_6238_:
{
lean_object* v_forbiddenNatModules_6241_; uint8_t v___x_6242_; 
v_forbiddenNatModules_6241_ = lean_ctor_get(v_a_6237_, 4);
lean_inc_ref(v_forbiddenNatModules_6241_);
lean_dec(v_a_6237_);
v___x_6242_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_6241_, v_type_6214_);
lean_dec_ref(v_forbiddenNatModules_6241_);
if (v___x_6242_ == 0)
{
lean_object* v___x_6243_; 
lean_del_object(v___x_6239_);
lean_inc_ref(v_type_6214_);
v___x_6243_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_6214_, v_a_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_);
if (lean_obj_tag(v___x_6243_) == 0)
{
lean_object* v_a_6244_; lean_object* v___x_6246_; uint8_t v_isShared_6247_; uint8_t v_isSharedCheck_6294_; 
v_a_6244_ = lean_ctor_get(v___x_6243_, 0);
v_isSharedCheck_6294_ = !lean_is_exclusive(v___x_6243_);
if (v_isSharedCheck_6294_ == 0)
{
v___x_6246_ = v___x_6243_;
v_isShared_6247_ = v_isSharedCheck_6294_;
goto v_resetjp_6245_;
}
else
{
lean_inc(v_a_6244_);
lean_dec(v___x_6243_);
v___x_6246_ = lean_box(0);
v_isShared_6247_ = v_isSharedCheck_6294_;
goto v_resetjp_6245_;
}
v_resetjp_6245_:
{
uint8_t v___x_6248_; 
v___x_6248_ = lean_unbox(v_a_6244_);
lean_dec(v_a_6244_);
if (v___x_6248_ == 0)
{
lean_object* v___x_6249_; 
lean_del_object(v___x_6246_);
v___x_6249_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6215_, v_a_6223_);
if (lean_obj_tag(v___x_6249_) == 0)
{
lean_object* v_a_6250_; lean_object* v___x_6252_; uint8_t v_isShared_6253_; uint8_t v_isSharedCheck_6281_; 
v_a_6250_ = lean_ctor_get(v___x_6249_, 0);
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6249_);
if (v_isSharedCheck_6281_ == 0)
{
v___x_6252_ = v___x_6249_;
v_isShared_6253_ = v_isSharedCheck_6281_;
goto v_resetjp_6251_;
}
else
{
lean_inc(v_a_6250_);
lean_dec(v___x_6249_);
v___x_6252_ = lean_box(0);
v_isShared_6253_ = v_isSharedCheck_6281_;
goto v_resetjp_6251_;
}
v_resetjp_6251_:
{
lean_object* v_natTypeIdOf_6254_; lean_object* v___x_6255_; 
v_natTypeIdOf_6254_ = lean_ctor_get(v_a_6250_, 6);
lean_inc_ref(v_natTypeIdOf_6254_);
lean_dec(v_a_6250_);
v___x_6255_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_6254_, v_type_6214_);
lean_dec_ref(v_natTypeIdOf_6254_);
if (lean_obj_tag(v___x_6255_) == 1)
{
lean_object* v_val_6256_; lean_object* v___x_6258_; 
lean_dec_ref(v_type_6214_);
v_val_6256_ = lean_ctor_get(v___x_6255_, 0);
lean_inc(v_val_6256_);
lean_dec_ref_known(v___x_6255_, 1);
if (v_isShared_6253_ == 0)
{
lean_ctor_set(v___x_6252_, 0, v_val_6256_);
v___x_6258_ = v___x_6252_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_val_6256_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
else
{
lean_object* v___x_6260_; 
lean_dec(v___x_6255_);
lean_del_object(v___x_6252_);
lean_inc_ref(v_type_6214_);
v___x_6260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_6214_, v_a_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_, v_a_6224_);
if (lean_obj_tag(v___x_6260_) == 0)
{
lean_object* v_a_6261_; lean_object* v___f_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; 
v_a_6261_ = lean_ctor_get(v___x_6260_, 0);
lean_inc_n(v_a_6261_, 2);
lean_dec_ref_known(v___x_6260_, 1);
v___f_6262_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_6262_, 0, v_type_6214_);
lean_closure_set(v___f_6262_, 1, v_a_6261_);
v___x_6263_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_6264_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6263_, v___f_6262_, v_a_6215_);
if (lean_obj_tag(v___x_6264_) == 0)
{
lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6271_; 
v_isSharedCheck_6271_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6271_ == 0)
{
lean_object* v_unused_6272_; 
v_unused_6272_ = lean_ctor_get(v___x_6264_, 0);
lean_dec(v_unused_6272_);
v___x_6266_ = v___x_6264_;
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
else
{
lean_dec(v___x_6264_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6271_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6269_; 
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 0, v_a_6261_);
v___x_6269_ = v___x_6266_;
goto v_reusejp_6268_;
}
else
{
lean_object* v_reuseFailAlloc_6270_; 
v_reuseFailAlloc_6270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6270_, 0, v_a_6261_);
v___x_6269_ = v_reuseFailAlloc_6270_;
goto v_reusejp_6268_;
}
v_reusejp_6268_:
{
return v___x_6269_;
}
}
}
else
{
lean_object* v_a_6273_; lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6280_; 
lean_dec(v_a_6261_);
v_a_6273_ = lean_ctor_get(v___x_6264_, 0);
v_isSharedCheck_6280_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6280_ == 0)
{
v___x_6275_ = v___x_6264_;
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
else
{
lean_inc(v_a_6273_);
lean_dec(v___x_6264_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
lean_object* v___x_6278_; 
if (v_isShared_6276_ == 0)
{
v___x_6278_ = v___x_6275_;
goto v_reusejp_6277_;
}
else
{
lean_object* v_reuseFailAlloc_6279_; 
v_reuseFailAlloc_6279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_a_6273_);
v___x_6278_ = v_reuseFailAlloc_6279_;
goto v_reusejp_6277_;
}
v_reusejp_6277_:
{
return v___x_6278_;
}
}
}
}
else
{
lean_dec_ref(v_type_6214_);
return v___x_6260_;
}
}
}
}
else
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6289_; 
lean_dec_ref(v_type_6214_);
v_a_6282_ = lean_ctor_get(v___x_6249_, 0);
v_isSharedCheck_6289_ = !lean_is_exclusive(v___x_6249_);
if (v_isSharedCheck_6289_ == 0)
{
v___x_6284_ = v___x_6249_;
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v___x_6249_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v___x_6287_; 
if (v_isShared_6285_ == 0)
{
v___x_6287_ = v___x_6284_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_a_6282_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
}
}
else
{
lean_object* v___x_6290_; lean_object* v___x_6292_; 
lean_dec_ref(v_type_6214_);
v___x_6290_ = lean_box(0);
if (v_isShared_6247_ == 0)
{
lean_ctor_set(v___x_6246_, 0, v___x_6290_);
v___x_6292_ = v___x_6246_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6293_; 
v_reuseFailAlloc_6293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6293_, 0, v___x_6290_);
v___x_6292_ = v_reuseFailAlloc_6293_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
return v___x_6292_;
}
}
}
}
else
{
lean_object* v_a_6295_; lean_object* v___x_6297_; uint8_t v_isShared_6298_; uint8_t v_isSharedCheck_6302_; 
lean_dec_ref(v_type_6214_);
v_a_6295_ = lean_ctor_get(v___x_6243_, 0);
v_isSharedCheck_6302_ = !lean_is_exclusive(v___x_6243_);
if (v_isSharedCheck_6302_ == 0)
{
v___x_6297_ = v___x_6243_;
v_isShared_6298_ = v_isSharedCheck_6302_;
goto v_resetjp_6296_;
}
else
{
lean_inc(v_a_6295_);
lean_dec(v___x_6243_);
v___x_6297_ = lean_box(0);
v_isShared_6298_ = v_isSharedCheck_6302_;
goto v_resetjp_6296_;
}
v_resetjp_6296_:
{
lean_object* v___x_6300_; 
if (v_isShared_6298_ == 0)
{
v___x_6300_ = v___x_6297_;
goto v_reusejp_6299_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6295_);
v___x_6300_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6299_;
}
v_reusejp_6299_:
{
return v___x_6300_;
}
}
}
}
else
{
lean_object* v___x_6303_; lean_object* v___x_6305_; 
lean_dec_ref(v_type_6214_);
v___x_6303_ = lean_box(0);
if (v_isShared_6240_ == 0)
{
lean_ctor_set(v___x_6239_, 0, v___x_6303_);
v___x_6305_ = v___x_6239_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v___x_6303_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
else
{
lean_object* v_a_6308_; lean_object* v___x_6310_; uint8_t v_isShared_6311_; uint8_t v_isSharedCheck_6315_; 
lean_dec_ref(v_type_6214_);
v_a_6308_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6315_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6315_ == 0)
{
v___x_6310_ = v___x_6236_;
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
else
{
lean_inc(v_a_6308_);
lean_dec(v___x_6236_);
v___x_6310_ = lean_box(0);
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
v_resetjp_6309_:
{
lean_object* v___x_6313_; 
if (v_isShared_6311_ == 0)
{
v___x_6313_ = v___x_6310_;
goto v_reusejp_6312_;
}
else
{
lean_object* v_reuseFailAlloc_6314_; 
v_reuseFailAlloc_6314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_a_6308_);
v___x_6313_ = v_reuseFailAlloc_6314_;
goto v_reusejp_6312_;
}
v_reusejp_6312_:
{
return v___x_6313_;
}
}
}
}
}
}
else
{
lean_object* v_a_6317_; lean_object* v___x_6319_; uint8_t v_isShared_6320_; uint8_t v_isSharedCheck_6324_; 
lean_dec_ref(v_type_6214_);
v_a_6317_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6324_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6324_ == 0)
{
v___x_6319_ = v___x_6226_;
v_isShared_6320_ = v_isSharedCheck_6324_;
goto v_resetjp_6318_;
}
else
{
lean_inc(v_a_6317_);
lean_dec(v___x_6226_);
v___x_6319_ = lean_box(0);
v_isShared_6320_ = v_isSharedCheck_6324_;
goto v_resetjp_6318_;
}
v_resetjp_6318_:
{
lean_object* v___x_6322_; 
if (v_isShared_6320_ == 0)
{
v___x_6322_ = v___x_6319_;
goto v_reusejp_6321_;
}
else
{
lean_object* v_reuseFailAlloc_6323_; 
v_reuseFailAlloc_6323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6323_, 0, v_a_6317_);
v___x_6322_ = v_reuseFailAlloc_6323_;
goto v_reusejp_6321_;
}
v_reusejp_6321_:
{
return v___x_6322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_, lean_object* v_a_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_){
_start:
{
lean_object* v_res_6337_; 
v_res_6337_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_6325_, v_a_6326_, v_a_6327_, v_a_6328_, v_a_6329_, v_a_6330_, v_a_6331_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_);
lean_dec(v_a_6335_);
lean_dec_ref(v_a_6334_);
lean_dec(v_a_6333_);
lean_dec_ref(v_a_6332_);
lean_dec(v_a_6331_);
lean_dec_ref(v_a_6330_);
lean_dec(v_a_6329_);
lean_dec_ref(v_a_6328_);
lean_dec(v_a_6327_);
lean_dec(v_a_6326_);
return v_res_6337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_6338_, lean_object* v_x_6339_, lean_object* v_x_6340_){
_start:
{
uint8_t v___x_6341_; 
v___x_6341_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_6339_, v_x_6340_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_6342_, lean_object* v_x_6343_, lean_object* v_x_6344_){
_start:
{
uint8_t v_res_6345_; lean_object* v_r_6346_; 
v_res_6345_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_6342_, v_x_6343_, v_x_6344_);
lean_dec_ref(v_x_6344_);
lean_dec_ref(v_x_6343_);
v_r_6346_ = lean_box(v_res_6345_);
return v_r_6346_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_6347_, lean_object* v_x_6348_, size_t v_x_6349_, lean_object* v_x_6350_){
_start:
{
uint8_t v___x_6351_; 
v___x_6351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6348_, v_x_6349_, v_x_6350_);
return v___x_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6352_, lean_object* v_x_6353_, lean_object* v_x_6354_, lean_object* v_x_6355_){
_start:
{
size_t v_x_10931__boxed_6356_; uint8_t v_res_6357_; lean_object* v_r_6358_; 
v_x_10931__boxed_6356_ = lean_unbox_usize(v_x_6354_);
lean_dec(v_x_6354_);
v_res_6357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_6352_, v_x_6353_, v_x_10931__boxed_6356_, v_x_6355_);
lean_dec_ref(v_x_6355_);
lean_dec_ref(v_x_6353_);
v_r_6358_ = lean_box(v_res_6357_);
return v_r_6358_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_6359_, lean_object* v_keys_6360_, lean_object* v_vals_6361_, lean_object* v_heq_6362_, lean_object* v_i_6363_, lean_object* v_k_6364_){
_start:
{
uint8_t v___x_6365_; 
v___x_6365_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_6360_, v_i_6363_, v_k_6364_);
return v___x_6365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_6366_, lean_object* v_keys_6367_, lean_object* v_vals_6368_, lean_object* v_heq_6369_, lean_object* v_i_6370_, lean_object* v_k_6371_){
_start:
{
uint8_t v_res_6372_; lean_object* v_r_6373_; 
v_res_6372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_6366_, v_keys_6367_, v_vals_6368_, v_heq_6369_, v_i_6370_, v_k_6371_);
lean_dec_ref(v_k_6371_);
lean_dec_ref(v_vals_6368_);
lean_dec_ref(v_keys_6367_);
v_r_6373_ = lean_box(v_res_6372_);
return v_r_6373_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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
