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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toZero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instHSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(131, 168, 246, 170, 1, 89, 173, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "nsmul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toIsPreorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(196, 84, 36, 174, 137, 182, 135, 55)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__49_value),LEAN_SCALAR_PTR_LITERAL(75, 224, 25, 76, 51, 82, 222, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "IsLinearOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toIsPartialOrder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__47_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(111, 211, 224, 54, 22, 32, 255, 113)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(83, 108, 214, 71, 226, 119, 72, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toAddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(205, 72, 3, 192, 99, 106, 67, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "AddCommGroup"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toAddCommMonoid"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(64, 158, 132, 153, 136, 140, 172, 182)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(143, 195, 31, 215, 150, 195, 138, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__61_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__63_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OrderedAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__65_value),LEAN_SCALAR_PTR_LITERAL(93, 134, 71, 250, 19, 181, 172, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 228, 118, 74, 233, 69, 129, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15;
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
lean_dec_ref(v___x_9_);
v___x_11_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_10_, v_a_3_);
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
lean_dec_ref(v___x_103_);
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
lean_dec_ref(v___x_149_);
v___x_151_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_150_, v_a_143_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_n(v_a_152_, 2);
lean_dec_ref(v___x_151_);
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
lean_dec_ref(v___x_800_);
v_lia_802_ = lean_ctor_get_uint8(v_a_801_, sizeof(void*)*12 + 23);
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
lean_dec_ref(v___x_803_);
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
lean_dec_ref(v___x_844_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_896_, lean_object* v_type_897_, lean_object* v_commRingInst_x3f_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_898_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_917_; 
v_val_904_ = lean_ctor_get(v_commRingInst_x3f_898_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_commRingInst_x3f_898_);
if (v_isSharedCheck_917_ == 0)
{
v___x_906_ = v_commRingInst_x3f_898_;
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_val_904_);
lean_dec(v_commRingInst_x3f_898_);
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
lean_ctor_set(v___x_910_, 0, v_u_896_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_mkConst(v___x_908_, v___x_910_);
v___x_912_ = l_Lean_mkAppB(v___x_911_, v_type_897_, v_val_904_);
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
lean_dec(v_commRingInst_x3f_898_);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v_u_896_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_mkConst(v___x_918_, v___x_920_);
v___x_922_ = l_Lean_Expr_app___override(v___x_921_, v_type_897_);
v___x_923_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_922_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_924_, lean_object* v_type_925_, lean_object* v_commRingInst_x3f_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_924_, v_type_925_, v_commRingInst_x3f_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_933_, lean_object* v_type_934_, lean_object* v_commRingInst_x3f_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_933_, v_type_934_, v_commRingInst_x3f_935_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_948_, lean_object* v_type_949_, lean_object* v_commRingInst_x3f_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_948_, v_type_949_, v_commRingInst_x3f_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
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
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_974_, lean_object* v_type_975_, lean_object* v_ringInst_x3f_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_976_) == 1)
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_995_; 
v_val_982_ = lean_ctor_get(v_ringInst_x3f_976_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_ringInst_x3f_976_);
if (v_isSharedCheck_995_ == 0)
{
v___x_984_ = v_ringInst_x3f_976_;
v_isShared_985_ = v_isSharedCheck_995_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v_ringInst_x3f_976_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_995_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_988_, 0, v_u_974_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_mkConst(v___x_986_, v___x_988_);
v___x_990_ = l_Lean_mkAppB(v___x_989_, v_type_975_, v_val_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_990_);
v___x_992_ = v___x_984_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_ringInst_x3f_976_);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v_u_974_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_mkConst(v___x_996_, v___x_998_);
v___x_1000_ = l_Lean_Expr_app___override(v___x_999_, v_type_975_);
v___x_1001_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1000_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1002_, lean_object* v_type_1003_, lean_object* v_ringInst_x3f_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1002_, v_type_1003_, v_ringInst_x3f_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1011_, lean_object* v_type_1012_, lean_object* v_ringInst_x3f_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1011_, v_type_1012_, v_ringInst_x3f_1013_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1026_, lean_object* v_type_1027_, lean_object* v_ringInst_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1026_, v_type_1027_, v_ringInst_x3f_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
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
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1052_, lean_object* v_type_1053_, lean_object* v_ringInst_x3f_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1054_) == 1)
{
lean_object* v_val_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1073_; 
v_val_1060_ = lean_ctor_get(v_ringInst_x3f_1054_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_ringInst_x3f_1054_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1062_ = v_ringInst_x3f_1054_;
v_isShared_1063_ = v_isSharedCheck_1073_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_val_1060_);
lean_dec(v_ringInst_x3f_1054_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1073_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_u_1052_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_mkConst(v___x_1064_, v___x_1066_);
v___x_1068_ = l_Lean_mkAppB(v___x_1067_, v_type_1053_, v_val_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1068_);
v___x_1070_ = v___x_1062_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v_ringInst_x3f_1054_);
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_u_1052_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_mkConst(v___x_1074_, v___x_1076_);
v___x_1078_ = l_Lean_Expr_app___override(v___x_1077_, v_type_1053_);
v___x_1079_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1078_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1080_, lean_object* v_type_1081_, lean_object* v_ringInst_x3f_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1080_, v_type_1081_, v_ringInst_x3f_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1089_, lean_object* v_type_1090_, lean_object* v_ringInst_x3f_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1089_, v_type_1090_, v_ringInst_x3f_1091_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1104_, lean_object* v_type_1105_, lean_object* v_ringInst_x3f_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1104_, v_type_1105_, v_ringInst_x3f_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec(v_a_1107_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1126_, lean_object* v_type_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_u_1126_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
lean_inc_ref(v___x_1141_);
v___x_1142_ = l_Lean_mkConst(v___x_1139_, v___x_1141_);
lean_inc_ref(v_type_1127_);
v___x_1143_ = l_Lean_Expr_app___override(v___x_1142_, v_type_1127_);
v___x_1144_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1143_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1226_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1226_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1226_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
if (lean_obj_tag(v_a_1145_) == 1)
{
lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1147_);
v_val_1149_ = lean_ctor_get(v_a_1145_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1151_ = v_a_1145_;
v_isShared_1152_ = v_isSharedCheck_1221_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_dec(v_a_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1221_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1154_ = l_Lean_mkConst(v___x_1153_, v___x_1141_);
lean_inc_ref(v_type_1127_);
v___x_1155_ = l_Lean_mkAppB(v___x_1154_, v_type_1127_, v_val_1149_);
v___x_1156_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1155_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1212_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1212_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1212_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = l_Lean_Meta_mkNumeral(v_type_1127_, v___x_1168_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc_n(v_a_1170_, 2);
lean_dec_ref(v___x_1169_);
lean_inc(v_a_1157_);
v___x_1171_ = l_Lean_Meta_isDefEqD(v_a_1157_, v_a_1170_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; uint8_t v___x_1173_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v___x_1173_ = lean_unbox(v_a_1172_);
lean_dec(v_a_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1176_; 
lean_inc(v_a_1157_);
v___x_1174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1157_, v_a_1170_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
v___x_1176_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1132_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = lean_unbox(v_a_1177_);
lean_dec(v_a_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_a_1175_);
goto v___jp_1161_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_Sym_reportIssue(v_a_1175_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_dec_ref(v___x_1179_);
goto v___jp_1161_;
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1159_);
lean_dec(v_a_1157_);
lean_del_object(v___x_1151_);
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1175_);
lean_del_object(v___x_1159_);
lean_dec(v_a_1157_);
lean_del_object(v___x_1151_);
v_a_1188_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1176_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1176_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_dec(v_a_1170_);
goto v___jp_1161_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_a_1170_);
lean_del_object(v___x_1159_);
lean_dec(v_a_1157_);
lean_del_object(v___x_1151_);
v_a_1196_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1171_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1171_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_del_object(v___x_1159_);
lean_dec(v_a_1157_);
lean_del_object(v___x_1151_);
v_a_1204_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1169_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1169_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
v___jp_1161_:
{
lean_object* v___x_1163_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_a_1157_);
v___x_1163_ = v___x_1151_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1157_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1163_);
v___x_1165_ = v___x_1159_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1151_);
lean_dec_ref(v_type_1127_);
v_a_1213_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1156_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1156_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
lean_dec(v_a_1145_);
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_type_1127_);
v___x_1222_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1222_);
v___x_1224_ = v___x_1147_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
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
else
{
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_type_1127_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1227_, lean_object* v_type_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1227_, v_type_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
return v_res_1240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1249_, lean_object* v_type_1250_, lean_object* v_semiringInst_x3f_1251_, lean_object* v_leInst_x3f_1252_, lean_object* v_ltInst_x3f_1253_, lean_object* v_preorderInst_x3f_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1251_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1252_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1253_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1254_) == 1)
{
lean_object* v_val_1265_; lean_object* v_val_1266_; lean_object* v_val_1267_; lean_object* v_val_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_isOrdType_1273_; lean_object* v___x_1274_; 
v_val_1265_ = lean_ctor_get(v_semiringInst_x3f_1251_, 0);
lean_inc(v_val_1265_);
lean_dec_ref(v_semiringInst_x3f_1251_);
v_val_1266_ = lean_ctor_get(v_leInst_x3f_1252_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v_leInst_x3f_1252_);
v_val_1267_ = lean_ctor_get(v_ltInst_x3f_1253_, 0);
lean_inc(v_val_1267_);
lean_dec_ref(v_ltInst_x3f_1253_);
v_val_1268_ = lean_ctor_get(v_preorderInst_x3f_1254_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v_preorderInst_x3f_1254_);
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_u_1249_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_mkConst(v___x_1269_, v___x_1271_);
v_isOrdType_1273_ = l_Lean_mkApp5(v___x_1272_, v_type_1250_, v_val_1265_, v_val_1266_, v_val_1267_, v_val_1268_);
lean_inc_ref(v_isOrdType_1273_);
v___x_1274_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_isOrdType_1273_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
if (lean_obj_tag(v_a_1275_) == 1)
{
lean_dec_ref(v_a_1275_);
lean_dec_ref(v_isOrdType_1273_);
return v___x_1274_;
}
else
{
lean_object* v___x_1276_; 
lean_dec_ref(v___x_1274_);
lean_dec(v_a_1275_);
v___x_1276_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1255_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; uint8_t v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = lean_unbox(v_a_1277_);
lean_dec(v_a_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v_isOrdType_1273_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1280_ = l_Lean_indentExpr(v_isOrdType_1273_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_Meta_Sym_reportIssue(v___x_1281_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_dec_ref(v___x_1282_);
goto v___jp_1262_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_isOrdType_1273_);
v_a_1291_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1276_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1276_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1273_);
return v___x_1274_;
}
}
else
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref(v_leInst_x3f_1252_);
lean_dec_ref(v_semiringInst_x3f_1251_);
lean_dec(v_preorderInst_x3f_1254_);
lean_dec_ref(v_type_1250_);
lean_dec(v_u_1249_);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_ltInst_x3f_1253_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_ltInst_x3f_1253_, 0);
lean_dec(v_unused_1307_);
v___x_1300_ = v_ltInst_x3f_1253_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v_ltInst_x3f_1253_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(0);
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_semiringInst_x3f_1251_);
lean_dec(v_preorderInst_x3f_1254_);
lean_dec(v_ltInst_x3f_1253_);
lean_dec_ref(v_type_1250_);
lean_dec(v_u_1249_);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_leInst_x3f_1252_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_leInst_x3f_1252_, 0);
lean_dec(v_unused_1316_);
v___x_1309_ = v_leInst_x3f_1252_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v_leInst_x3f_1252_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_preorderInst_x3f_1254_);
lean_dec(v_ltInst_x3f_1253_);
lean_dec(v_leInst_x3f_1252_);
lean_dec_ref(v_type_1250_);
lean_dec(v_u_1249_);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_semiringInst_x3f_1251_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_semiringInst_x3f_1251_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v_semiringInst_x3f_1251_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_semiringInst_x3f_1251_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v_preorderInst_x3f_1254_);
lean_dec(v_ltInst_x3f_1253_);
lean_dec(v_leInst_x3f_1252_);
lean_dec(v_semiringInst_x3f_1251_);
lean_dec_ref(v_type_1250_);
lean_dec(v_u_1249_);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
return v___x_1327_;
}
v___jp_1262_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1328_, lean_object* v_type_1329_, lean_object* v_semiringInst_x3f_1330_, lean_object* v_leInst_x3f_1331_, lean_object* v_ltInst_x3f_1332_, lean_object* v_preorderInst_x3f_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1328_, v_type_1329_, v_semiringInst_x3f_1330_, v_leInst_x3f_1331_, v_ltInst_x3f_1332_, v_preorderInst_x3f_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1342_, lean_object* v_type_1343_, lean_object* v_semiringInst_x3f_1344_, lean_object* v_leInst_x3f_1345_, lean_object* v_ltInst_x3f_1346_, lean_object* v_preorderInst_x3f_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1342_, v_type_1343_, v_semiringInst_x3f_1344_, v_leInst_x3f_1345_, v_ltInst_x3f_1346_, v_preorderInst_x3f_1347_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1360_ = _args[0];
lean_object* v_type_1361_ = _args[1];
lean_object* v_semiringInst_x3f_1362_ = _args[2];
lean_object* v_leInst_x3f_1363_ = _args[3];
lean_object* v_ltInst_x3f_1364_ = _args[4];
lean_object* v_preorderInst_x3f_1365_ = _args[5];
lean_object* v_a_1366_ = _args[6];
lean_object* v_a_1367_ = _args[7];
lean_object* v_a_1368_ = _args[8];
lean_object* v_a_1369_ = _args[9];
lean_object* v_a_1370_ = _args[10];
lean_object* v_a_1371_ = _args[11];
lean_object* v_a_1372_ = _args[12];
lean_object* v_a_1373_ = _args[13];
lean_object* v_a_1374_ = _args[14];
lean_object* v_a_1375_ = _args[15];
lean_object* v_a_1376_ = _args[16];
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1360_, v_type_1361_, v_semiringInst_x3f_1362_, v_leInst_x3f_1363_, v_ltInst_x3f_1364_, v_preorderInst_x3f_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1388_, lean_object* v_type_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_natModuleType_1399_; lean_object* v___x_1400_; 
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_u_1388_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_inc_ref(v___x_1397_);
v___x_1398_ = l_Lean_mkConst(v___x_1395_, v___x_1397_);
lean_inc_ref(v_type_1389_);
v_natModuleType_1399_ = l_Lean_Expr_app___override(v___x_1398_, v_type_1389_);
v___x_1400_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_natModuleType_1399_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1414_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1414_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
if (lean_obj_tag(v_a_1401_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_del_object(v___x_1403_);
v_val_1405_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_val_1405_);
lean_dec_ref(v_a_1401_);
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1407_ = l_Lean_mkConst(v___x_1406_, v___x_1397_);
v___x_1408_ = l_Lean_mkAppB(v___x_1407_, v_type_1389_, v_val_1405_);
v___x_1409_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1408_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_dec(v_a_1401_);
lean_dec_ref(v___x_1397_);
lean_dec_ref(v_type_1389_);
v___x_1410_ = lean_box(0);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1410_);
v___x_1412_ = v___x_1403_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_dec_ref(v___x_1397_);
lean_dec_ref(v_type_1389_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1415_, lean_object* v_type_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1415_, v_type_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1423_, lean_object* v_type_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1423_, v_type_1424_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1437_, lean_object* v_type_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1437_, v_type_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec(v_a_1439_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1451_, lean_object* v_u_1452_, lean_object* v_type_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_u_1452_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_mkConst(v_declName_1451_, v___x_1460_);
v___x_1462_ = l_Lean_Expr_app___override(v___x_1461_, v_type_1453_);
v___x_1463_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1462_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1464_, lean_object* v_u_1465_, lean_object* v_type_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1464_, v_u_1465_, v_type_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1473_, lean_object* v_u_1474_, lean_object* v_type_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1473_, v_u_1474_, v_type_1475_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1488_, lean_object* v_u_1489_, lean_object* v_type_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1488_, v_u_1489_, v_type_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1503_, lean_object* v_u_1504_, lean_object* v_type_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_u_1504_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_mkConst(v_declName_1503_, v___x_1514_);
v___x_1516_ = l_Lean_Expr_app___override(v___x_1515_, v_type_1505_);
v___x_1517_ = l_Lean_Meta_Sym_synthInstance(v___x_1516_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1518_, lean_object* v_u_1519_, lean_object* v_type_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1518_, v_u_1519_, v_type_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1529_, lean_object* v_u_1530_, lean_object* v_type_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1529_, v_u_1530_, v_type_1531_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1544_, lean_object* v_u_1545_, lean_object* v_type_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1544_, v_u_1545_, v_type_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
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
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1559_, lean_object* v_u_1560_, lean_object* v_type_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1569_ = lean_box(0);
lean_inc_n(v_u_1560_, 2);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_u_1560_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_u_1560_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_u_1560_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = l_Lean_mkConst(v_declName_1559_, v___x_1572_);
lean_inc_ref_n(v_type_1561_, 2);
v___x_1574_ = l_Lean_mkApp3(v___x_1573_, v_type_1561_, v_type_1561_, v_type_1561_);
v___x_1575_ = l_Lean_Meta_Sym_synthInstance(v___x_1574_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1576_, lean_object* v_u_1577_, lean_object* v_type_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1576_, v_u_1577_, v_type_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1587_, lean_object* v_u_1588_, lean_object* v_type_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1587_, v_u_1588_, v_type_1589_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1602_, lean_object* v_u_1603_, lean_object* v_type_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1602_, v_u_1603_, v_type_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec(v_a_1605_);
return v_res_1616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = l_Lean_Level_ofNat(v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1622_, lean_object* v_type_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1633_ = lean_box(0);
lean_inc(v_u_1622_);
v___x_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_u_1622_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_u_1622_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_mkConst(v___x_1631_, v___x_1636_);
v___x_1638_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1623_);
v___x_1639_ = l_Lean_mkApp3(v___x_1637_, v___x_1638_, v_type_1623_, v_type_1623_);
v___x_1640_ = l_Lean_Meta_Sym_synthInstance(v___x_1639_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1641_, lean_object* v_type_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1641_, v_type_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1651_, lean_object* v_type_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1651_, v_type_1652_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1665_, lean_object* v_type_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1665_, v_type_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1679_, lean_object* v_type_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1690_ = lean_box(0);
lean_inc(v_u_1679_);
v___x_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_u_1679_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_u_1679_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1689_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_mkConst(v___x_1688_, v___x_1693_);
v___x_1695_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1680_);
v___x_1696_ = l_Lean_mkApp3(v___x_1694_, v___x_1695_, v_type_1680_, v_type_1680_);
v___x_1697_ = l_Lean_Meta_Sym_synthInstance(v___x_1696_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1698_, lean_object* v_type_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1698_, v_type_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1708_, lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1708_, v_type_1709_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1722_, lean_object* v_type_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1722_, v_type_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec(v_a_1724_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1736_, lean_object* v_parentInst_x3f_1737_, lean_object* v_childInst_x3f_1738_, lean_object* v_toFieldName_1739_, lean_object* v_u_1740_, lean_object* v_type_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1736_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1737_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1738_) == 1)
{
lean_object* v_val_1752_; lean_object* v_val_1753_; lean_object* v_val_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_toField_1758_; lean_object* v___x_1759_; 
v_val_1752_ = lean_ctor_get(v_leInst_x3f_1736_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v_leInst_x3f_1736_);
v_val_1753_ = lean_ctor_get(v_parentInst_x3f_1737_, 0);
lean_inc_n(v_val_1753_, 2);
lean_dec_ref(v_parentInst_x3f_1737_);
v_val_1754_ = lean_ctor_get(v_childInst_x3f_1738_, 0);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_u_1740_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_mkConst(v_toFieldName_1739_, v___x_1756_);
lean_inc(v_val_1754_);
v_toField_1758_ = l_Lean_mkApp3(v___x_1757_, v_type_1741_, v_val_1752_, v_val_1754_);
lean_inc_ref(v_toField_1758_);
v___x_1759_ = l_Lean_Meta_isDefEqD(v_val_1753_, v_toField_1758_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1790_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1790_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1790_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_unbox(v_a_1760_);
lean_dec(v_a_1760_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1762_);
lean_dec_ref(v_childInst_x3f_1738_);
v___x_1765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1753_, v_toField_1758_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1742_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; uint8_t v___x_1769_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_unbox(v_a_1768_);
lean_dec(v_a_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v_a_1766_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Meta_Sym_reportIssue(v_a_1766_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_dec_ref(v___x_1770_);
goto v___jp_1749_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_a_1766_);
v_a_1779_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1767_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1767_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v___x_1788_; 
lean_dec_ref(v_toField_1758_);
lean_dec(v_val_1753_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v_childInst_x3f_1738_);
v___x_1788_ = v___x_1762_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_childInst_x3f_1738_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v_toField_1758_);
lean_dec(v_val_1753_);
lean_dec_ref(v_childInst_x3f_1738_);
v_a_1791_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1759_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1759_);
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
else
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v_leInst_x3f_1736_);
lean_dec_ref(v_type_1741_);
lean_dec(v_u_1740_);
lean_dec(v_toFieldName_1739_);
lean_dec(v_childInst_x3f_1738_);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_parentInst_x3f_1737_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_parentInst_x3f_1737_, 0);
lean_dec(v_unused_1807_);
v___x_1800_ = v_parentInst_x3f_1737_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v_parentInst_x3f_1737_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
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
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_type_1741_);
lean_dec(v_u_1740_);
lean_dec(v_toFieldName_1739_);
lean_dec(v_childInst_x3f_1738_);
lean_dec(v_parentInst_x3f_1737_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_leInst_x3f_1736_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_leInst_x3f_1736_, 0);
lean_dec(v_unused_1816_);
v___x_1809_ = v_leInst_x3f_1736_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_leInst_x3f_1736_);
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
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v_type_1741_);
lean_dec(v_u_1740_);
lean_dec(v_toFieldName_1739_);
lean_dec(v_childInst_x3f_1738_);
lean_dec(v_parentInst_x3f_1737_);
lean_dec(v_leInst_x3f_1736_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1819_, lean_object* v_parentInst_x3f_1820_, lean_object* v_childInst_x3f_1821_, lean_object* v_toFieldName_1822_, lean_object* v_u_1823_, lean_object* v_type_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1819_, v_parentInst_x3f_1820_, v_childInst_x3f_1821_, v_toFieldName_1822_, v_u_1823_, v_type_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1833_, lean_object* v_parentInst_x3f_1834_, lean_object* v_childInst_x3f_1835_, lean_object* v_toFieldName_1836_, lean_object* v_u_1837_, lean_object* v_type_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1833_, v_parentInst_x3f_1834_, v_childInst_x3f_1835_, v_toFieldName_1836_, v_u_1837_, v_type_1838_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1851_ = _args[0];
lean_object* v_parentInst_x3f_1852_ = _args[1];
lean_object* v_childInst_x3f_1853_ = _args[2];
lean_object* v_toFieldName_1854_ = _args[3];
lean_object* v_u_1855_ = _args[4];
lean_object* v_type_1856_ = _args[5];
lean_object* v_a_1857_ = _args[6];
lean_object* v_a_1858_ = _args[7];
lean_object* v_a_1859_ = _args[8];
lean_object* v_a_1860_ = _args[9];
lean_object* v_a_1861_ = _args[10];
lean_object* v_a_1862_ = _args[11];
lean_object* v_a_1863_ = _args[12];
lean_object* v_a_1864_ = _args[13];
lean_object* v_a_1865_ = _args[14];
lean_object* v_a_1866_ = _args[15];
lean_object* v_a_1867_ = _args[16];
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1851_, v_parentInst_x3f_1852_, v_childInst_x3f_1853_, v_toFieldName_1854_, v_u_1855_, v_type_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec(v_a_1857_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1869_, lean_object* v_inst_1870_, lean_object* v_toFieldName_1871_, lean_object* v_u_1872_, lean_object* v_type_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_toField_1882_; lean_object* v___x_1883_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_u_1872_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_mkConst(v_toFieldName_1871_, v___x_1880_);
v_toField_1882_ = l_Lean_mkAppB(v___x_1881_, v_type_1873_, v_inst_1870_);
v___x_1883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1869_, v_toField_1882_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1884_, lean_object* v_inst_1885_, lean_object* v_toFieldName_1886_, lean_object* v_u_1887_, lean_object* v_type_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1884_, v_inst_1885_, v_toFieldName_1886_, v_u_1887_, v_type_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1895_, lean_object* v_inst_1896_, lean_object* v_toFieldName_1897_, lean_object* v_u_1898_, lean_object* v_type_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1895_, v_inst_1896_, v_toFieldName_1897_, v_u_1898_, v_type_1899_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1912_, lean_object* v_inst_1913_, lean_object* v_toFieldName_1914_, lean_object* v_u_1915_, lean_object* v_type_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1912_, v_inst_1913_, v_toFieldName_1914_, v_u_1915_, v_type_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1929_, lean_object* v_inst_1930_, lean_object* v_toFieldName_1931_, lean_object* v_toHeteroName_1932_, lean_object* v_u_1933_, lean_object* v_type_1934_, lean_object* v_extraType_x3f_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_toField_1944_; 
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v_u_1933_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_inc_ref(v___x_1942_);
v___x_1943_ = l_Lean_mkConst(v_toFieldName_1931_, v___x_1942_);
lean_inc_ref(v_type_1934_);
v_toField_1944_ = l_Lean_mkAppB(v___x_1943_, v_type_1934_, v_inst_1930_);
if (lean_obj_tag(v_extraType_x3f_1935_) == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = l_Lean_mkConst(v_toHeteroName_1932_, v___x_1942_);
v___x_1946_ = l_Lean_mkAppB(v___x_1945_, v_type_1934_, v_toField_1944_);
v___x_1947_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1929_, v___x_1946_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1947_;
}
else
{
lean_object* v_val_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_val_1948_ = lean_ctor_get(v_extraType_x3f_1935_, 0);
lean_inc(v_val_1948_);
lean_dec_ref(v_extraType_x3f_1935_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1942_);
v___x_1951_ = l_Lean_mkConst(v_toHeteroName_1932_, v___x_1950_);
v___x_1952_ = l_Lean_mkApp3(v___x_1951_, v_val_1948_, v_type_1934_, v_toField_1944_);
v___x_1953_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1929_, v___x_1952_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1954_, lean_object* v_inst_1955_, lean_object* v_toFieldName_1956_, lean_object* v_toHeteroName_1957_, lean_object* v_u_1958_, lean_object* v_type_1959_, lean_object* v_extraType_x3f_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1954_, v_inst_1955_, v_toFieldName_1956_, v_toHeteroName_1957_, v_u_1958_, v_type_1959_, v_extraType_x3f_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_1967_, lean_object* v_inst_1968_, lean_object* v_toFieldName_1969_, lean_object* v_toHeteroName_1970_, lean_object* v_u_1971_, lean_object* v_type_1972_, lean_object* v_extraType_x3f_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1967_, v_inst_1968_, v_toFieldName_1969_, v_toHeteroName_1970_, v_u_1971_, v_type_1972_, v_extraType_x3f_1973_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_1986_ = _args[0];
lean_object* v_inst_1987_ = _args[1];
lean_object* v_toFieldName_1988_ = _args[2];
lean_object* v_toHeteroName_1989_ = _args[3];
lean_object* v_u_1990_ = _args[4];
lean_object* v_type_1991_ = _args[5];
lean_object* v_extraType_x3f_1992_ = _args[6];
lean_object* v_a_1993_ = _args[7];
lean_object* v_a_1994_ = _args[8];
lean_object* v_a_1995_ = _args[9];
lean_object* v_a_1996_ = _args[10];
lean_object* v_a_1997_ = _args[11];
lean_object* v_a_1998_ = _args[12];
lean_object* v_a_1999_ = _args[13];
lean_object* v_a_2000_ = _args[14];
lean_object* v_a_2001_ = _args[15];
lean_object* v_a_2002_ = _args[16];
lean_object* v_a_2003_ = _args[17];
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_1986_, v_inst_1987_, v_toFieldName_1988_, v_toHeteroName_1989_, v_u_1990_, v_type_1991_, v_extraType_x3f_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec(v_a_1993_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2009_, lean_object* v_type_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_smulType_2026_; lean_object* v___x_2027_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2020_ = lean_box(0);
lean_inc(v_u_2009_);
v___x_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_u_2009_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_u_2009_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2019_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
lean_inc_ref(v___x_2023_);
v___x_2024_ = l_Lean_mkConst(v___x_2018_, v___x_2023_);
v___x_2025_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2010_, 2);
v_smulType_2026_ = l_Lean_mkApp3(v___x_2024_, v___x_2025_, v_type_2010_, v_type_2010_);
v___x_2027_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_smulType_2026_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2064_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2064_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2064_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
if (lean_obj_tag(v_a_2028_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2059_; 
lean_del_object(v___x_2030_);
v_val_2032_ = lean_ctor_get(v_a_2028_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_a_2028_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2034_ = v_a_2028_;
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v_a_2028_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2059_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2037_ = l_Lean_mkConst(v___x_2036_, v___x_2023_);
lean_inc_ref(v_type_2010_);
v___x_2038_ = l_Lean_mkApp4(v___x_2037_, v___x_2025_, v_type_2010_, v_type_2010_, v_val_2032_);
v___x_2039_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2038_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2050_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2050_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2040_);
v___x_2045_ = v___x_2034_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2047_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2034_);
v_a_2051_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2039_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2039_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
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
else
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v_a_2028_);
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_type_2010_);
v___x_2060_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2060_);
v___x_2062_ = v___x_2030_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_type_2010_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2065_, lean_object* v_type_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2065_, v_type_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2075_, lean_object* v_type_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2075_, v_type_2076_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2089_, lean_object* v_type_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2089_, v_type_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec(v_a_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2103_, lean_object* v_type_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_smulType_2120_; lean_object* v___x_2121_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2113_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2114_ = lean_box(0);
lean_inc(v_u_2103_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_u_2103_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_u_2103_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2113_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
lean_inc_ref(v___x_2117_);
v___x_2118_ = l_Lean_mkConst(v___x_2112_, v___x_2117_);
v___x_2119_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2104_, 2);
v_smulType_2120_ = l_Lean_mkApp3(v___x_2118_, v___x_2119_, v_type_2104_, v_type_2104_);
v___x_2121_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_smulType_2120_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2158_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2158_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2158_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2124_);
v_val_2126_ = lean_ctor_get(v_a_2122_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2122_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2128_ = v_a_2122_;
v_isShared_2129_ = v_isSharedCheck_2153_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_val_2126_);
lean_dec(v_a_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2153_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2131_ = l_Lean_mkConst(v___x_2130_, v___x_2117_);
lean_inc_ref(v_type_2104_);
v___x_2132_ = l_Lean_mkApp4(v___x_2131_, v___x_2119_, v_type_2104_, v_type_2104_, v_val_2126_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2132_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2144_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2144_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2144_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_a_2134_);
v___x_2139_ = v___x_2128_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_2128_);
v_a_2145_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2133_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2133_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
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
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec(v_a_2122_);
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_type_2104_);
v___x_2154_ = lean_box(0);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2154_);
v___x_2156_ = v___x_2124_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_dec_ref(v___x_2117_);
lean_dec_ref(v_type_2104_);
return v___x_2121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2159_, lean_object* v_type_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2159_, v_type_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2169_, lean_object* v_type_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2169_, v_type_2170_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2183_, lean_object* v_type_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2183_, v_type_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec(v_a_2185_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v_ks_2201_; lean_object* v_vs_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2226_; 
v_ks_2201_ = lean_ctor_get(v_x_2197_, 0);
v_vs_2202_ = lean_ctor_get(v_x_2197_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2204_ = v_x_2197_;
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_vs_2202_);
lean_inc(v_ks_2201_);
lean_dec(v_x_2197_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_array_get_size(v_ks_2201_);
v___x_2207_ = lean_nat_dec_lt(v_x_2198_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_dec(v_x_2198_);
v___x_2208_ = lean_array_push(v_ks_2201_, v_x_2199_);
v___x_2209_ = lean_array_push(v_vs_2202_, v_x_2200_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2209_);
lean_ctor_set(v___x_2204_, 0, v___x_2208_);
v___x_2211_ = v___x_2204_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
else
{
lean_object* v_k_x27_2213_; uint8_t v___x_2214_; 
v_k_x27_2213_ = lean_array_fget_borrowed(v_ks_2201_, v_x_2198_);
v___x_2214_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2199_, v_k_x27_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2216_; 
if (v_isShared_2205_ == 0)
{
v___x_2216_ = v___x_2204_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_ks_2201_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_vs_2202_);
v___x_2216_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_unsigned_to_nat(1u);
v___x_2218_ = lean_nat_add(v_x_2198_, v___x_2217_);
lean_dec(v_x_2198_);
v_x_2197_ = v___x_2216_;
v_x_2198_ = v___x_2218_;
goto _start;
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_array_fset(v_ks_2201_, v_x_2198_, v_x_2199_);
v___x_2222_ = lean_array_fset(v_vs_2202_, v_x_2198_, v_x_2200_);
lean_dec(v_x_2198_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2222_);
lean_ctor_set(v___x_2204_, 0, v___x_2221_);
v___x_2224_ = v___x_2204_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2227_, lean_object* v_k_2228_, lean_object* v_v_2229_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(0u);
v___x_2231_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2227_, v___x_2230_, v_k_2228_, v_v_2229_);
return v___x_2231_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; 
v___x_2232_ = ((size_t)5ULL);
v___x_2233_ = ((size_t)1ULL);
v___x_2234_ = lean_usize_shift_left(v___x_2233_, v___x_2232_);
return v___x_2234_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; 
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2237_ = lean_usize_sub(v___x_2236_, v___x_2235_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(lean_object* v_x_2239_, size_t v_x_2240_, size_t v_x_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_){
_start:
{
if (lean_obj_tag(v_x_2239_) == 0)
{
lean_object* v_es_2244_; size_t v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; lean_object* v_j_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_es_2244_ = lean_ctor_get(v_x_2239_, 0);
v___x_2245_ = ((size_t)5ULL);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_2248_ = lean_usize_land(v_x_2240_, v___x_2247_);
v_j_2249_ = lean_usize_to_nat(v___x_2248_);
v___x_2250_ = lean_array_get_size(v_es_2244_);
v___x_2251_ = lean_nat_dec_lt(v_j_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_dec(v_j_2249_);
lean_dec(v_x_2243_);
lean_dec_ref(v_x_2242_);
return v_x_2239_;
}
else
{
lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2288_; 
lean_inc_ref(v_es_2244_);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_x_2239_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v_x_2239_, 0);
lean_dec(v_unused_2289_);
v___x_2253_ = v_x_2239_;
v_isShared_2254_ = v_isSharedCheck_2288_;
goto v_resetjp_2252_;
}
else
{
lean_dec(v_x_2239_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2288_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_v_2255_; lean_object* v___x_2256_; lean_object* v_xs_x27_2257_; lean_object* v___y_2259_; 
v_v_2255_ = lean_array_fget(v_es_2244_, v_j_2249_);
v___x_2256_ = lean_box(0);
v_xs_x27_2257_ = lean_array_fset(v_es_2244_, v_j_2249_, v___x_2256_);
switch(lean_obj_tag(v_v_2255_))
{
case 0:
{
lean_object* v_key_2264_; lean_object* v_val_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2275_; 
v_key_2264_ = lean_ctor_get(v_v_2255_, 0);
v_val_2265_ = lean_ctor_get(v_v_2255_, 1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_v_2255_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2267_ = v_v_2255_;
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_val_2265_);
lean_inc(v_key_2264_);
lean_dec(v_v_2255_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2275_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
uint8_t v___x_2269_; 
v___x_2269_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2242_, v_key_2264_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_del_object(v___x_2267_);
v___x_2270_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2264_, v_val_2265_, v_x_2242_, v_x_2243_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___y_2259_ = v___x_2271_;
goto v___jp_2258_;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_val_2265_);
lean_dec(v_key_2264_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v_x_2243_);
lean_ctor_set(v___x_2267_, 0, v_x_2242_);
v___x_2273_ = v___x_2267_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_x_2242_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_x_2243_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
v___y_2259_ = v___x_2273_;
goto v___jp_2258_;
}
}
}
}
case 1:
{
lean_object* v_node_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2286_; 
v_node_2276_ = lean_ctor_get(v_v_2255_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_v_2255_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2278_ = v_v_2255_;
v_isShared_2279_ = v_isSharedCheck_2286_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_node_2276_);
lean_dec(v_v_2255_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2286_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2280_ = lean_usize_shift_right(v_x_2240_, v___x_2245_);
v___x_2281_ = lean_usize_add(v_x_2241_, v___x_2246_);
v___x_2282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_node_2276_, v___x_2280_, v___x_2281_, v_x_2242_, v_x_2243_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2282_);
v___x_2284_ = v___x_2278_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
v___y_2259_ = v___x_2284_;
goto v___jp_2258_;
}
}
}
default: 
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_x_2242_);
lean_ctor_set(v___x_2287_, 1, v_x_2243_);
v___y_2259_ = v___x_2287_;
goto v___jp_2258_;
}
}
v___jp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_array_fset(v_xs_x27_2257_, v_j_2249_, v___y_2259_);
lean_dec(v_j_2249_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2260_);
v___x_2262_ = v___x_2253_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v_ks_2290_; lean_object* v_vs_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2311_; 
v_ks_2290_ = lean_ctor_get(v_x_2239_, 0);
v_vs_2291_ = lean_ctor_get(v_x_2239_, 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_x_2239_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2293_ = v_x_2239_;
v_isShared_2294_ = v_isSharedCheck_2311_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_vs_2291_);
lean_inc(v_ks_2290_);
lean_dec(v_x_2239_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2311_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_ks_2290_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_vs_2291_);
v___x_2296_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v_newNode_2297_; uint8_t v___y_2299_; size_t v___x_2305_; uint8_t v___x_2306_; 
v_newNode_2297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(v___x_2296_, v_x_2242_, v_x_2243_);
v___x_2305_ = ((size_t)7ULL);
v___x_2306_ = lean_usize_dec_le(v___x_2305_, v_x_2241_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2297_);
v___x_2308_ = lean_unsigned_to_nat(4u);
v___x_2309_ = lean_nat_dec_lt(v___x_2307_, v___x_2308_);
lean_dec(v___x_2307_);
v___y_2299_ = v___x_2309_;
goto v___jp_2298_;
}
else
{
v___y_2299_ = v___x_2306_;
goto v___jp_2298_;
}
v___jp_2298_:
{
if (v___y_2299_ == 0)
{
lean_object* v_ks_2300_; lean_object* v_vs_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_ks_2300_ = lean_ctor_get(v_newNode_2297_, 0);
lean_inc_ref(v_ks_2300_);
v_vs_2301_ = lean_ctor_get(v_newNode_2297_, 1);
lean_inc_ref(v_vs_2301_);
lean_dec_ref(v_newNode_2297_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__2);
v___x_2304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_x_2241_, v_ks_2300_, v_vs_2301_, v___x_2302_, v___x_2303_);
lean_dec_ref(v_vs_2301_);
lean_dec_ref(v_ks_2300_);
return v___x_2304_;
}
else
{
return v_newNode_2297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2312_, lean_object* v_keys_2313_, lean_object* v_vals_2314_, lean_object* v_i_2315_, lean_object* v_entries_2316_){
_start:
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = lean_array_get_size(v_keys_2313_);
v___x_2318_ = lean_nat_dec_lt(v_i_2315_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_dec(v_i_2315_);
return v_entries_2316_;
}
else
{
lean_object* v_k_2319_; lean_object* v_v_2320_; uint64_t v___x_2321_; size_t v_h_2322_; size_t v___x_2323_; lean_object* v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; size_t v_h_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_k_2319_ = lean_array_fget_borrowed(v_keys_2313_, v_i_2315_);
v_v_2320_ = lean_array_fget_borrowed(v_vals_2314_, v_i_2315_);
v___x_2321_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2319_);
v_h_2322_ = lean_uint64_to_usize(v___x_2321_);
v___x_2323_ = ((size_t)5ULL);
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = ((size_t)1ULL);
v___x_2326_ = lean_usize_sub(v_depth_2312_, v___x_2325_);
v___x_2327_ = lean_usize_mul(v___x_2323_, v___x_2326_);
v_h_2328_ = lean_usize_shift_right(v_h_2322_, v___x_2327_);
v___x_2329_ = lean_nat_add(v_i_2315_, v___x_2324_);
lean_dec(v_i_2315_);
lean_inc(v_v_2320_);
lean_inc(v_k_2319_);
v___x_2330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_entries_2316_, v_h_2328_, v_depth_2312_, v_k_2319_, v_v_2320_);
v_i_2315_ = v___x_2329_;
v_entries_2316_ = v___x_2330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2332_, lean_object* v_keys_2333_, lean_object* v_vals_2334_, lean_object* v_i_2335_, lean_object* v_entries_2336_){
_start:
{
size_t v_depth_boxed_2337_; lean_object* v_res_2338_; 
v_depth_boxed_2337_ = lean_unbox_usize(v_depth_2332_);
lean_dec(v_depth_2332_);
v_res_2338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2337_, v_keys_2333_, v_vals_2334_, v_i_2335_, v_entries_2336_);
lean_dec_ref(v_vals_2334_);
lean_dec_ref(v_keys_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
size_t v_x_575187__boxed_2344_; size_t v_x_575188__boxed_2345_; lean_object* v_res_2346_; 
v_x_575187__boxed_2344_ = lean_unbox_usize(v_x_2340_);
lean_dec(v_x_2340_);
v_x_575188__boxed_2345_ = lean_unbox_usize(v_x_2341_);
lean_dec(v_x_2341_);
v_res_2346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_2339_, v_x_575187__boxed_2344_, v_x_575188__boxed_2345_, v_x_2342_, v_x_2343_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
uint64_t v___x_2350_; size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2348_);
v___x_2351_ = lean_uint64_to_usize(v___x_2350_);
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_2347_, v___x_2351_, v___x_2352_, v_x_2348_, v_x_2349_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0(lean_object* v_type_2354_, lean_object* v_s_2355_){
_start:
{
lean_object* v_structs_2356_; lean_object* v_typeIdOf_2357_; lean_object* v_exprToStructId_2358_; lean_object* v_exprToStructIdEntries_2359_; lean_object* v_forbiddenNatModules_2360_; lean_object* v_natStructs_2361_; lean_object* v_natTypeIdOf_2362_; lean_object* v_exprToNatStructId_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2372_; 
v_structs_2356_ = lean_ctor_get(v_s_2355_, 0);
v_typeIdOf_2357_ = lean_ctor_get(v_s_2355_, 1);
v_exprToStructId_2358_ = lean_ctor_get(v_s_2355_, 2);
v_exprToStructIdEntries_2359_ = lean_ctor_get(v_s_2355_, 3);
v_forbiddenNatModules_2360_ = lean_ctor_get(v_s_2355_, 4);
v_natStructs_2361_ = lean_ctor_get(v_s_2355_, 5);
v_natTypeIdOf_2362_ = lean_ctor_get(v_s_2355_, 6);
v_exprToNatStructId_2363_ = lean_ctor_get(v_s_2355_, 7);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_s_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2365_ = v_s_2355_;
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_exprToNatStructId_2363_);
lean_inc(v_natTypeIdOf_2362_);
lean_inc(v_natStructs_2361_);
lean_inc(v_forbiddenNatModules_2360_);
lean_inc(v_exprToStructIdEntries_2359_);
lean_inc(v_exprToStructId_2358_);
lean_inc(v_typeIdOf_2357_);
lean_inc(v_structs_2356_);
lean_dec(v_s_2355_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2367_ = lean_box(0);
v___x_2368_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_forbiddenNatModules_2360_, v_type_2354_, v___x_2367_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 4, v___x_2368_);
v___x_2370_ = v___x_2365_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_structs_2356_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_typeIdOf_2357_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_exprToStructId_2358_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_exprToStructIdEntries_2359_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2371_, 5, v_natStructs_2361_);
lean_ctor_set(v_reuseFailAlloc_2371_, 6, v_natTypeIdOf_2362_);
lean_ctor_set(v_reuseFailAlloc_2371_, 7, v_exprToNatStructId_2363_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(lean_object* v_a_2373_, lean_object* v_00___2374_){
_start:
{
if (lean_obj_tag(v_a_2373_) == 0)
{
uint8_t v___x_2375_; 
v___x_2375_ = 0;
return v___x_2375_;
}
else
{
uint8_t v___x_2376_; 
v___x_2376_ = 1;
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1___boxed(lean_object* v_a_2377_, lean_object* v_00___2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2377_, v_00___2378_);
lean_dec(v_a_2377_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2(lean_object* v___x_2381_, lean_object* v_s_2382_){
_start:
{
lean_object* v_structs_2383_; lean_object* v_typeIdOf_2384_; lean_object* v_exprToStructId_2385_; lean_object* v_exprToStructIdEntries_2386_; lean_object* v_forbiddenNatModules_2387_; lean_object* v_natStructs_2388_; lean_object* v_natTypeIdOf_2389_; lean_object* v_exprToNatStructId_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_structs_2383_ = lean_ctor_get(v_s_2382_, 0);
v_typeIdOf_2384_ = lean_ctor_get(v_s_2382_, 1);
v_exprToStructId_2385_ = lean_ctor_get(v_s_2382_, 2);
v_exprToStructIdEntries_2386_ = lean_ctor_get(v_s_2382_, 3);
v_forbiddenNatModules_2387_ = lean_ctor_get(v_s_2382_, 4);
v_natStructs_2388_ = lean_ctor_get(v_s_2382_, 5);
v_natTypeIdOf_2389_ = lean_ctor_get(v_s_2382_, 6);
v_exprToNatStructId_2390_ = lean_ctor_get(v_s_2382_, 7);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_s_2382_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v_s_2382_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_exprToNatStructId_2390_);
lean_inc(v_natTypeIdOf_2389_);
lean_inc(v_natStructs_2388_);
lean_inc(v_forbiddenNatModules_2387_);
lean_inc(v_exprToStructIdEntries_2386_);
lean_inc(v_exprToStructId_2385_);
lean_inc(v_typeIdOf_2384_);
lean_inc(v_structs_2383_);
lean_dec(v_s_2382_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = lean_array_push(v_structs_2383_, v___x_2381_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_typeIdOf_2384_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_exprToStructId_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_exprToStructIdEntries_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_forbiddenNatModules_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 5, v_natStructs_2388_);
lean_ctor_set(v_reuseFailAlloc_2397_, 6, v_natTypeIdOf_2389_);
lean_ctor_set(v_reuseFailAlloc_2397_, 7, v_exprToNatStructId_2390_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_unsigned_to_nat(32u);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__5);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = l_Lean_mkRawNatLit(v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = l_Lean_Int_mkType;
v___x_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = l_Lean_Nat_mkType;
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___y_2532_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; uint8_t v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; uint8_t v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___x_2597_; 
lean_inc_ref(v_type_2519_);
v___x_2597_ = l_Lean_Meta_getDecLevel_x3f(v_type_2519_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_3515_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_3515_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_3515_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
if (lean_obj_tag(v_a_2598_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_3510_; 
lean_del_object(v___x_2600_);
v_val_2602_ = lean_ctor_get(v_a_2598_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_2604_ = v_a_2598_;
v_isShared_2605_ = v_isSharedCheck_3510_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_val_2602_);
lean_dec(v_a_2598_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_3510_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; 
lean_inc_ref(v_type_2519_);
v___x_2606_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_3509_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_3509_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_3509_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2611_, v_val_2602_, v_type_2519_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2614_, v_val_2602_, v_type_2519_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc_n(v_a_2616_, 2);
lean_dec_ref(v___x_2615_);
lean_inc(v_a_2613_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2617_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_2616_, v_a_2613_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v_homomulFn_x3f_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; lean_object* v___y_2715_; lean_object* v_ltFn_x3f_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; uint8_t v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v_leFn_x3f_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_charInst_x3f_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___x_3130_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
lean_inc(v_a_2613_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3130_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_2613_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
lean_inc(v_a_2613_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3132_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_2613_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
lean_inc(v_a_2613_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3134_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_2613_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3157_; lean_object* v___x_3244_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v___x_3244_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2522_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; uint8_t v_ring_3246_; lean_object* v___f_3247_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3346_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
v_ring_3246_ = lean_ctor_get_uint8(v_a_3245_, sizeof(void*)*12 + 21);
lean_dec(v_a_3245_);
lean_inc_ref(v_type_2519_);
v___f_3247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_3247_, 0, v_type_2519_);
if (v_ring_3246_ == 0)
{
v___y_3346_ = v_ring_3246_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = lean_box(0);
v___x_3432_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2607_, v___x_3431_);
if (v___x_3432_ == 0)
{
v___y_3346_ = v___x_3432_;
goto v___jp_3345_;
}
else
{
if (lean_obj_tag(v_a_3131_) == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v___x_3433_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3433_, v___f_3247_, v_a_2520_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3442_; 
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; 
v_unused_3443_ = lean_ctor_get(v___x_3434_, 0);
lean_dec(v_unused_3443_);
v___x_3436_ = v___x_3434_;
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v___x_3434_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_box(0);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3438_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3434_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3434_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = 0;
v___y_3346_ = v___x_3452_;
goto v___jp_3345_;
}
}
}
v___jp_3248_:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3259_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; uint8_t v_ring_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3270_);
v_ring_3272_ = lean_ctor_get_uint8(v_a_3271_, sizeof(void*)*12 + 21);
lean_dec(v_a_3271_);
if (v_ring_3272_ == 0)
{
lean_dec_ref(v___f_3247_);
v___y_3137_ = v___y_3249_;
v___y_3138_ = v___y_3269_;
v___y_3139_ = v___y_3250_;
v___y_3140_ = v___y_3251_;
v___y_3141_ = v___y_3252_;
v___y_3142_ = v___y_3253_;
v___y_3143_ = v___y_3254_;
v___y_3144_ = v___y_3255_;
v___y_3145_ = v___y_3256_;
v___y_3146_ = v___y_3257_;
v___y_3147_ = v___y_3258_;
v___y_3148_ = v___y_3259_;
v___y_3149_ = v___y_3261_;
v___y_3150_ = v___y_3260_;
v___y_3151_ = v___y_3262_;
v___y_3152_ = v___y_3263_;
v___y_3153_ = v___y_3264_;
v___y_3154_ = v___y_3265_;
v___y_3155_ = v___y_3266_;
v___y_3156_ = v___y_3267_;
v___y_3157_ = v_ring_3272_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_box(0);
v___x_3274_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__1(v_a_2607_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec_ref(v___f_3247_);
v___y_3137_ = v___y_3249_;
v___y_3138_ = v___y_3269_;
v___y_3139_ = v___y_3250_;
v___y_3140_ = v___y_3251_;
v___y_3141_ = v___y_3252_;
v___y_3142_ = v___y_3253_;
v___y_3143_ = v___y_3254_;
v___y_3144_ = v___y_3255_;
v___y_3145_ = v___y_3256_;
v___y_3146_ = v___y_3257_;
v___y_3147_ = v___y_3258_;
v___y_3148_ = v___y_3259_;
v___y_3149_ = v___y_3261_;
v___y_3150_ = v___y_3260_;
v___y_3151_ = v___y_3262_;
v___y_3152_ = v___y_3263_;
v___y_3153_ = v___y_3264_;
v___y_3154_ = v___y_3265_;
v___y_3155_ = v___y_3266_;
v___y_3156_ = v___y_3267_;
v___y_3157_ = v___x_3274_;
goto v___jp_3136_;
}
else
{
if (lean_obj_tag(v___y_3269_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec(v___y_3266_);
lean_dec(v___y_3260_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v___x_3275_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3276_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3275_, v___f_3247_, v___y_3254_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3284_; 
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; 
v_unused_3285_ = lean_ctor_get(v___x_3276_, 0);
lean_dec(v_unused_3285_);
v___x_3278_ = v___x_3276_;
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
else
{
lean_dec(v___x_3276_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3284_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_box(0);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3280_);
v___x_3282_ = v___x_3278_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3276_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3276_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_dec_ref(v___f_3247_);
v___y_3137_ = v___y_3249_;
v___y_3138_ = v___y_3269_;
v___y_3139_ = v___y_3250_;
v___y_3140_ = v___y_3251_;
v___y_3141_ = v___y_3252_;
v___y_3142_ = v___y_3253_;
v___y_3143_ = v___y_3254_;
v___y_3144_ = v___y_3255_;
v___y_3145_ = v___y_3256_;
v___y_3146_ = v___y_3257_;
v___y_3147_ = v___y_3258_;
v___y_3148_ = v___y_3259_;
v___y_3149_ = v___y_3261_;
v___y_3150_ = v___y_3260_;
v___y_3151_ = v___y_3262_;
v___y_3152_ = v___y_3263_;
v___y_3153_ = v___y_3264_;
v___y_3154_ = v___y_3265_;
v___y_3155_ = v___y_3266_;
v___y_3156_ = v___y_3267_;
v___y_3157_ = v___y_3268_;
goto v___jp_3136_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v___y_3269_);
lean_dec(v___y_3266_);
lean_dec(v___y_3260_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3294_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3270_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3270_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
v___jp_3302_:
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_box(0);
v___y_3249_ = v___y_3303_;
v___y_3250_ = v___y_3304_;
v___y_3251_ = v___y_3305_;
v___y_3252_ = v___y_3306_;
v___y_3253_ = v___y_3307_;
v___y_3254_ = v___y_3308_;
v___y_3255_ = v___y_3309_;
v___y_3256_ = v___y_3310_;
v___y_3257_ = v___y_3311_;
v___y_3258_ = v___y_3312_;
v___y_3259_ = v___y_3313_;
v___y_3260_ = v___y_3315_;
v___y_3261_ = v___y_3314_;
v___y_3262_ = v___y_3316_;
v___y_3263_ = v___y_3317_;
v___y_3264_ = v___y_3318_;
v___y_3265_ = v___y_3319_;
v___y_3266_ = v___y_3320_;
v___y_3267_ = v___y_3321_;
v___y_3268_ = v___y_3322_;
v___y_3269_ = v___x_3323_;
goto v___jp_3248_;
}
v___jp_3324_:
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_box(0);
v___y_3303_ = v___y_3325_;
v___y_3304_ = v___x_3344_;
v___y_3305_ = v___y_3327_;
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3329_;
v___y_3308_ = v___y_3334_;
v___y_3309_ = v___y_3330_;
v___y_3310_ = v___y_3343_;
v___y_3311_ = v___y_3331_;
v___y_3312_ = v___y_3337_;
v___y_3313_ = v___y_3336_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3340_;
v___y_3317_ = v___y_3338_;
v___y_3318_ = v___y_3335_;
v___y_3319_ = v___y_3342_;
v___y_3320_ = v___y_3332_;
v___y_3321_ = v___y_3341_;
v___y_3322_ = v___y_3333_;
goto v___jp_3302_;
}
v___jp_3345_:
{
lean_object* v___x_3347_; 
lean_inc(v_a_2607_);
v___x_3347_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2607_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc_n(v_a_3348_, 2);
lean_dec_ref(v___x_3347_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_3348_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc_n(v_a_3350_, 2);
lean_dec_ref(v___x_3349_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_3350_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3406_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3406_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3406_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
if (lean_obj_tag(v_a_3352_) == 1)
{
lean_object* v_val_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_del_object(v___x_3354_);
v_val_3356_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_val_3356_);
lean_dec_ref(v_a_3352_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3357_, v_val_2602_, v_type_2519_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_n(v_a_3359_, 2);
lean_dec_ref(v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64));
v___x_3361_ = lean_box(0);
lean_inc_n(v_val_2602_, 3);
v___x_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_val_2602_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
lean_inc_ref(v___x_3362_);
v___x_3363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_val_2602_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
lean_inc_ref(v___x_3363_);
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v_val_2602_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
lean_inc_ref(v___x_3364_);
v___x_3365_ = l_Lean_mkConst(v___x_3360_, v___x_3364_);
lean_inc_ref_n(v_type_2519_, 3);
v___x_3366_ = l_Lean_mkApp4(v___x_3365_, v_type_2519_, v_type_2519_, v_type_2519_, v_a_3359_);
v___x_3367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3366_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3367_) == 0)
{
if (lean_obj_tag(v_a_2613_) == 1)
{
if (lean_obj_tag(v_a_3131_) == 1)
{
lean_object* v_a_3368_; lean_object* v_val_3369_; lean_object* v_val_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v_val_3369_ = lean_ctor_get(v_a_2613_, 0);
v_val_3370_ = lean_ctor_get(v_a_3131_, 0);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66));
lean_inc_ref(v___x_3362_);
v___x_3372_ = l_Lean_mkConst(v___x_3371_, v___x_3362_);
lean_inc(v_val_3370_);
lean_inc(v_val_3369_);
lean_inc(v_a_3359_);
lean_inc_ref(v_type_2519_);
v___x_3373_ = l_Lean_mkApp4(v___x_3372_, v_type_2519_, v_a_3359_, v_val_3369_, v_val_3370_);
v___x_3374_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_3373_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
if (lean_obj_tag(v_a_3375_) == 0)
{
lean_dec_ref(v_a_3131_);
v___y_3303_ = v_val_3356_;
v___y_3304_ = v_a_3375_;
v___y_3305_ = v_a_3359_;
v___y_3306_ = v___x_3363_;
v___y_3307_ = v_a_3348_;
v___y_3308_ = v_a_2520_;
v___y_3309_ = v_a_3368_;
v___y_3310_ = v_a_2529_;
v___y_3311_ = v_a_3350_;
v___y_3312_ = v_a_2523_;
v___y_3313_ = v_a_2522_;
v___y_3314_ = v_a_2525_;
v___y_3315_ = v___x_3362_;
v___y_3316_ = v_a_2526_;
v___y_3317_ = v_a_2524_;
v___y_3318_ = v_a_2521_;
v___y_3319_ = v_a_2528_;
v___y_3320_ = v___x_3364_;
v___y_3321_ = v_a_2527_;
v___y_3322_ = v___y_3346_;
goto v___jp_3302_;
}
else
{
if (v___y_3346_ == 0)
{
v___y_3249_ = v_val_3356_;
v___y_3250_ = v_a_3375_;
v___y_3251_ = v_a_3359_;
v___y_3252_ = v___x_3363_;
v___y_3253_ = v_a_3348_;
v___y_3254_ = v_a_2520_;
v___y_3255_ = v_a_3368_;
v___y_3256_ = v_a_2529_;
v___y_3257_ = v_a_3350_;
v___y_3258_ = v_a_2523_;
v___y_3259_ = v_a_2522_;
v___y_3260_ = v___x_3362_;
v___y_3261_ = v_a_2525_;
v___y_3262_ = v_a_2526_;
v___y_3263_ = v_a_2524_;
v___y_3264_ = v_a_2521_;
v___y_3265_ = v_a_2528_;
v___y_3266_ = v___x_3364_;
v___y_3267_ = v_a_2527_;
v___y_3268_ = v___y_3346_;
v___y_3269_ = v_a_3131_;
goto v___jp_3248_;
}
else
{
lean_dec_ref(v_a_3131_);
v___y_3303_ = v_val_3356_;
v___y_3304_ = v_a_3375_;
v___y_3305_ = v_a_3359_;
v___y_3306_ = v___x_3363_;
v___y_3307_ = v_a_3348_;
v___y_3308_ = v_a_2520_;
v___y_3309_ = v_a_3368_;
v___y_3310_ = v_a_2529_;
v___y_3311_ = v_a_3350_;
v___y_3312_ = v_a_2523_;
v___y_3313_ = v_a_2522_;
v___y_3314_ = v_a_2525_;
v___y_3315_ = v___x_3362_;
v___y_3316_ = v_a_2526_;
v___y_3317_ = v_a_2524_;
v___y_3318_ = v_a_2521_;
v___y_3319_ = v_a_2528_;
v___y_3320_ = v___x_3364_;
v___y_3321_ = v_a_2527_;
v___y_3322_ = v___y_3346_;
goto v___jp_3302_;
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v_a_2613_);
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3363_);
lean_dec_ref(v___x_3362_);
lean_dec(v_a_3359_);
lean_dec(v_val_3356_);
lean_dec(v_a_3350_);
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3376_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3374_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_a_3384_; 
lean_dec(v_a_3131_);
v_a_3384_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3384_);
lean_dec_ref(v___x_3367_);
v___y_3325_ = v_val_3356_;
v___y_3326_ = v___x_3362_;
v___y_3327_ = v_a_3359_;
v___y_3328_ = v___x_3363_;
v___y_3329_ = v_a_3348_;
v___y_3330_ = v_a_3384_;
v___y_3331_ = v_a_3350_;
v___y_3332_ = v___x_3364_;
v___y_3333_ = v___y_3346_;
v___y_3334_ = v_a_2520_;
v___y_3335_ = v_a_2521_;
v___y_3336_ = v_a_2522_;
v___y_3337_ = v_a_2523_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3385_; 
lean_dec(v_a_3131_);
v_a_3385_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3367_);
v___y_3325_ = v_val_3356_;
v___y_3326_ = v___x_3362_;
v___y_3327_ = v_a_3359_;
v___y_3328_ = v___x_3363_;
v___y_3329_ = v_a_3348_;
v___y_3330_ = v_a_3385_;
v___y_3331_ = v_a_3350_;
v___y_3332_ = v___x_3364_;
v___y_3333_ = v___y_3346_;
v___y_3334_ = v_a_2520_;
v___y_3335_ = v_a_2521_;
v___y_3336_ = v_a_2522_;
v___y_3337_ = v_a_2523_;
v___y_3338_ = v_a_2524_;
v___y_3339_ = v_a_2525_;
v___y_3340_ = v_a_2526_;
v___y_3341_ = v_a_2527_;
v___y_3342_ = v_a_2528_;
v___y_3343_ = v_a_2529_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3363_);
lean_dec_ref(v___x_3362_);
lean_dec(v_a_3359_);
lean_dec(v_val_3356_);
lean_dec(v_a_3350_);
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3386_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3367_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3367_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_val_3356_);
lean_dec(v_a_3350_);
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3394_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3358_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3358_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
lean_dec(v_a_3352_);
lean_dec(v_a_3350_);
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v___x_3402_ = lean_box(0);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3402_);
v___x_3404_ = v___x_3354_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3350_);
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3407_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3351_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3351_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_a_3348_);
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3415_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3349_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3349_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v___f_3247_);
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3423_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3347_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3347_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v_a_3135_);
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3453_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3244_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3244_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
v___jp_3136_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__50));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc(v___y_3138_);
lean_inc(v_a_2613_);
v___x_3159_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2613_, v___y_3138_, v_a_3133_, v___x_3158_, v_val_2602_, v_type_2519_, v___y_3152_, v___y_3149_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__53));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc(v_a_2613_);
v___x_3162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2613_, v_a_3160_, v_a_3135_, v___x_3161_, v_val_2602_, v_type_2519_, v___y_3152_, v___y_3149_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__55));
lean_inc_n(v___y_3150_, 2);
v___x_3168_ = l_Lean_mkConst(v___x_3167_, v___y_3150_);
lean_inc_ref(v___y_3137_);
lean_inc_ref_n(v_type_2519_, 3);
v___x_3169_ = l_Lean_mkAppB(v___x_3168_, v_type_2519_, v___y_3137_);
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__56));
v___x_3171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__58));
v___x_3172_ = l_Lean_mkConst(v___x_3171_, v___y_3150_);
lean_inc_ref(v___x_3169_);
v___x_3173_ = l_Lean_mkAppB(v___x_3172_, v_type_2519_, v___x_3169_);
lean_inc(v___y_3146_);
lean_inc(v_val_2602_);
v___x_3174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2602_, v_type_2519_, v___y_3146_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__60));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3176_, v_val_2602_, v_type_2519_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2602_, v_type_2519_, v___y_3143_, v___y_3153_, v___y_3148_, v___y_3147_, v___y_3152_, v___y_3149_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
lean_inc(v___y_3138_);
lean_inc(v_a_2616_);
lean_inc(v_a_2613_);
lean_inc(v_a_3175_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2602_, v_type_2519_, v_a_3175_, v_a_2613_, v_a_2616_, v___y_3138_, v___y_3152_, v___y_3149_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3181_) == 0)
{
if (lean_obj_tag(v_a_3175_) == 1)
{
lean_object* v_a_3182_; lean_object* v_val_3183_; lean_object* v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3181_);
v_val_3183_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_val_3183_);
lean_dec_ref(v_a_3175_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_3184_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_2602_, v_type_2519_, v_val_3183_, v___y_3143_, v___y_3153_, v___y_3148_, v___y_3147_, v___y_3152_, v___y_3149_, v___y_3151_, v___y_3156_, v___y_3154_, v___y_3145_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v___y_2828_ = v___y_3137_;
v___y_2829_ = v_a_3178_;
v___y_2830_ = v___x_3165_;
v___y_2831_ = v___y_3138_;
v___y_2832_ = v___y_3140_;
v___y_2833_ = v___y_3139_;
v___y_2834_ = v_a_3163_;
v___y_2835_ = v___y_3141_;
v___y_2836_ = v___y_3142_;
v___y_2837_ = v___y_3146_;
v___y_2838_ = v___y_3144_;
v___y_2839_ = v___x_3170_;
v___y_2840_ = v_a_3182_;
v___y_2841_ = v___y_3150_;
v___y_2842_ = v___x_3166_;
v___y_2843_ = v_a_3180_;
v___y_2844_ = v___x_3173_;
v___y_2845_ = v___x_3169_;
v___y_2846_ = v___y_3157_;
v___y_2847_ = v___x_3164_;
v___y_2848_ = v___y_3155_;
v_charInst_x3f_2849_ = v_a_3185_;
v___y_2850_ = v___y_3143_;
v___y_2851_ = v___y_3153_;
v___y_2852_ = v___y_3148_;
v___y_2853_ = v___y_3147_;
v___y_2854_ = v___y_3152_;
v___y_2855_ = v___y_3149_;
v___y_2856_ = v___y_3151_;
v___y_2857_ = v___y_3156_;
v___y_2858_ = v___y_3154_;
v___y_2859_ = v___y_3145_;
goto v___jp_2827_;
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_a_3182_);
lean_dec(v_a_3180_);
lean_dec(v_a_3178_);
lean_dec_ref(v___x_3173_);
lean_dec_ref(v___x_3169_);
lean_dec(v_a_3163_);
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3186_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3184_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3195_; 
lean_dec(v_a_3175_);
v_a_3194_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3181_);
v___x_3195_ = lean_box(0);
v___y_2828_ = v___y_3137_;
v___y_2829_ = v_a_3178_;
v___y_2830_ = v___x_3165_;
v___y_2831_ = v___y_3138_;
v___y_2832_ = v___y_3140_;
v___y_2833_ = v___y_3139_;
v___y_2834_ = v_a_3163_;
v___y_2835_ = v___y_3141_;
v___y_2836_ = v___y_3142_;
v___y_2837_ = v___y_3146_;
v___y_2838_ = v___y_3144_;
v___y_2839_ = v___x_3170_;
v___y_2840_ = v_a_3194_;
v___y_2841_ = v___y_3150_;
v___y_2842_ = v___x_3166_;
v___y_2843_ = v_a_3180_;
v___y_2844_ = v___x_3173_;
v___y_2845_ = v___x_3169_;
v___y_2846_ = v___y_3157_;
v___y_2847_ = v___x_3164_;
v___y_2848_ = v___y_3155_;
v_charInst_x3f_2849_ = v___x_3195_;
v___y_2850_ = v___y_3143_;
v___y_2851_ = v___y_3153_;
v___y_2852_ = v___y_3148_;
v___y_2853_ = v___y_3147_;
v___y_2854_ = v___y_3152_;
v___y_2855_ = v___y_3149_;
v___y_2856_ = v___y_3151_;
v___y_2857_ = v___y_3156_;
v___y_2858_ = v___y_3154_;
v___y_2859_ = v___y_3145_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_a_3180_);
lean_dec(v_a_3178_);
lean_dec(v_a_3175_);
lean_dec_ref(v___x_3173_);
lean_dec_ref(v___x_3169_);
lean_dec(v_a_3163_);
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3196_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3181_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3181_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_a_3178_);
lean_dec(v_a_3175_);
lean_dec_ref(v___x_3173_);
lean_dec_ref(v___x_3169_);
lean_dec(v_a_3163_);
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3204_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3179_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3179_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_a_3175_);
lean_dec_ref(v___x_3173_);
lean_dec_ref(v___x_3169_);
lean_dec(v_a_3163_);
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3212_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3177_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3177_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v___x_3173_);
lean_dec_ref(v___x_3169_);
lean_dec(v_a_3163_);
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3220_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3174_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3174_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3228_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3162_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3162_);
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
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v___y_3155_);
lean_dec(v___y_3150_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_a_3135_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3236_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3159_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3159_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3461_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3134_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3134_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_a_3131_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3469_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3132_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3132_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3477_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3130_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3130_);
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
v___jp_2619_:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2645_, v___y_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_structs_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2655_);
v_structs_2657_ = lean_ctor_get(v_a_2656_, 0);
lean_inc_ref(v_structs_2657_);
lean_dec(v_a_2656_);
v___x_2658_ = lean_array_get_size(v_structs_2657_);
lean_dec_ref(v_structs_2657_);
v___x_2659_ = lean_unsigned_to_nat(32u);
v___x_2660_ = lean_mk_empty_array_with_capacity(v___x_2659_);
v___x_2661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__4);
v___x_2662_ = ((size_t)5ULL);
lean_inc(v___y_2620_);
v___x_2663_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2660_);
lean_ctor_set(v___x_2663_, 2, v___y_2620_);
lean_ctor_set(v___x_2663_, 3, v___y_2620_);
lean_ctor_set_usize(v___x_2663_, 4, v___x_2662_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__6);
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_box(0);
lean_inc_ref_n(v___x_2663_, 7);
lean_inc(v___y_2639_);
lean_inc(v___y_2641_);
lean_inc(v___y_2623_);
lean_inc(v___y_2635_);
lean_inc(v___y_2634_);
v___x_2667_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2667_, 0, v___x_2658_);
lean_ctor_set(v___x_2667_, 1, v_a_2607_);
lean_ctor_set(v___x_2667_, 2, v_type_2519_);
lean_ctor_set(v___x_2667_, 3, v_val_2602_);
lean_ctor_set(v___x_2667_, 4, v___y_2622_);
lean_ctor_set(v___x_2667_, 5, v_a_2613_);
lean_ctor_set(v___x_2667_, 6, v_a_2616_);
lean_ctor_set(v___x_2667_, 7, v_a_2618_);
lean_ctor_set(v___x_2667_, 8, v___y_2625_);
lean_ctor_set(v___x_2667_, 9, v___y_2627_);
lean_ctor_set(v___x_2667_, 10, v___y_2628_);
lean_ctor_set(v___x_2667_, 11, v___y_2640_);
lean_ctor_set(v___x_2667_, 12, v___y_2634_);
lean_ctor_set(v___x_2667_, 13, v___y_2632_);
lean_ctor_set(v___x_2667_, 14, v___y_2635_);
lean_ctor_set(v___x_2667_, 15, v___y_2623_);
lean_ctor_set(v___x_2667_, 16, v___y_2641_);
lean_ctor_set(v___x_2667_, 17, v___y_2643_);
lean_ctor_set(v___x_2667_, 18, v___y_2629_);
lean_ctor_set(v___x_2667_, 19, v___y_2639_);
lean_ctor_set(v___x_2667_, 20, v___y_2638_);
lean_ctor_set(v___x_2667_, 21, v___y_2626_);
lean_ctor_set(v___x_2667_, 22, v___y_2633_);
lean_ctor_set(v___x_2667_, 23, v___y_2631_);
lean_ctor_set(v___x_2667_, 24, v___y_2624_);
lean_ctor_set(v___x_2667_, 25, v___y_2636_);
lean_ctor_set(v___x_2667_, 26, v___y_2637_);
lean_ctor_set(v___x_2667_, 27, v_homomulFn_x3f_2644_);
lean_ctor_set(v___x_2667_, 28, v___y_2621_);
lean_ctor_set(v___x_2667_, 29, v___y_2630_);
lean_ctor_set(v___x_2667_, 30, v___x_2663_);
lean_ctor_set(v___x_2667_, 31, v___x_2664_);
lean_ctor_set(v___x_2667_, 32, v___x_2663_);
lean_ctor_set(v___x_2667_, 33, v___x_2663_);
lean_ctor_set(v___x_2667_, 34, v___x_2663_);
lean_ctor_set(v___x_2667_, 35, v___x_2663_);
lean_ctor_set(v___x_2667_, 36, v___x_2665_);
lean_ctor_set(v___x_2667_, 37, v___x_2664_);
lean_ctor_set(v___x_2667_, 38, v___x_2663_);
lean_ctor_set(v___x_2667_, 39, v___x_2666_);
lean_ctor_set(v___x_2667_, 40, v___x_2663_);
lean_ctor_set(v___x_2667_, 41, v___x_2663_);
lean_ctor_set_uint8(v___x_2667_, sizeof(void*)*42, v___y_2642_);
v___f_2668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2668_, 0, v___x_2667_);
v___x_2669_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2670_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2669_, v___f_2668_, v___y_2645_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_dec_ref(v___x_2670_);
if (lean_obj_tag(v___y_2639_) == 1)
{
if (lean_obj_tag(v___y_2634_) == 0)
{
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2641_);
lean_dec(v___y_2635_);
lean_dec(v___y_2623_);
v___y_2532_ = v___x_2658_;
goto v___jp_2531_;
}
else
{
lean_dec_ref(v___y_2634_);
if (lean_obj_tag(v___y_2635_) == 0)
{
if (v___y_2642_ == 0)
{
if (lean_obj_tag(v___y_2623_) == 0)
{
lean_object* v_val_2671_; uint8_t v___x_2672_; 
v_val_2671_ = lean_ctor_get(v___y_2639_, 0);
lean_inc(v_val_2671_);
lean_dec_ref(v___y_2639_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2641_);
lean_dec(v___y_2641_);
if (v___x_2672_ == 0)
{
lean_dec(v_val_2671_);
v___y_2532_ = v___x_2658_;
goto v___jp_2531_;
}
else
{
v___y_2547_ = v___y_2652_;
v___y_2548_ = v___y_2645_;
v___y_2549_ = v___y_2649_;
v___y_2550_ = v___y_2653_;
v___y_2551_ = v___y_2646_;
v___y_2552_ = v___y_2648_;
v___y_2553_ = v___x_2658_;
v___y_2554_ = v___y_2651_;
v___y_2555_ = v___y_2650_;
v___y_2556_ = v_val_2671_;
v___y_2557_ = v___y_2642_;
v___y_2558_ = v___y_2647_;
v___y_2559_ = v___y_2654_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_val_2673_; 
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2641_);
v_val_2673_ = lean_ctor_get(v___y_2639_, 0);
lean_inc(v_val_2673_);
lean_dec_ref(v___y_2639_);
v___y_2547_ = v___y_2652_;
v___y_2548_ = v___y_2645_;
v___y_2549_ = v___y_2649_;
v___y_2550_ = v___y_2653_;
v___y_2551_ = v___y_2646_;
v___y_2552_ = v___y_2648_;
v___y_2553_ = v___x_2658_;
v___y_2554_ = v___y_2651_;
v___y_2555_ = v___y_2650_;
v___y_2556_ = v_val_2673_;
v___y_2557_ = v___y_2642_;
v___y_2558_ = v___y_2647_;
v___y_2559_ = v___y_2654_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_val_2674_; 
lean_dec(v___y_2641_);
lean_dec(v___y_2623_);
v_val_2674_ = lean_ctor_get(v___y_2639_, 0);
lean_inc(v_val_2674_);
lean_dec_ref(v___y_2639_);
v___y_2572_ = v___y_2652_;
v___y_2573_ = v___y_2645_;
v___y_2574_ = v___y_2649_;
v___y_2575_ = v___y_2653_;
v___y_2576_ = v___y_2646_;
v___y_2577_ = v___y_2648_;
v___y_2578_ = v___x_2658_;
v___y_2579_ = v___y_2651_;
v___y_2580_ = v___y_2650_;
v___y_2581_ = v_val_2674_;
v___y_2582_ = v___y_2642_;
v___y_2583_ = v___y_2647_;
v___y_2584_ = v___y_2654_;
goto v___jp_2571_;
}
}
else
{
lean_object* v_val_2675_; 
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2641_);
lean_dec(v___y_2623_);
v_val_2675_ = lean_ctor_get(v___y_2639_, 0);
lean_inc(v_val_2675_);
lean_dec_ref(v___y_2639_);
v___y_2572_ = v___y_2652_;
v___y_2573_ = v___y_2645_;
v___y_2574_ = v___y_2649_;
v___y_2575_ = v___y_2653_;
v___y_2576_ = v___y_2646_;
v___y_2577_ = v___y_2648_;
v___y_2578_ = v___x_2658_;
v___y_2579_ = v___y_2651_;
v___y_2580_ = v___y_2650_;
v___y_2581_ = v_val_2675_;
v___y_2582_ = v___y_2642_;
v___y_2583_ = v___y_2647_;
v___y_2584_ = v___y_2654_;
goto v___jp_2571_;
}
}
}
else
{
lean_dec(v___y_2641_);
lean_dec(v___y_2639_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2623_);
v___y_2532_ = v___x_2658_;
goto v___jp_2531_;
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v___y_2641_);
lean_dec(v___y_2639_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2623_);
v_a_2676_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2670_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2670_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_homomulFn_x3f_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_dec(v_a_2607_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2684_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2655_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2655_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
v___jp_2692_:
{
lean_object* v___x_2727_; 
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2727_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2602_, v_type_2519_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2602_, v_type_2519_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2729_) == 0)
{
if (lean_obj_tag(v___y_2704_) == 0)
{
lean_object* v_a_2730_; 
lean_dec(v___y_2715_);
lean_del_object(v___x_2604_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v___y_2620_ = v___y_2693_;
v___y_2621_ = v___y_2694_;
v___y_2622_ = v___y_2695_;
v___y_2623_ = v___y_2696_;
v___y_2624_ = v___y_2697_;
v___y_2625_ = v___y_2698_;
v___y_2626_ = v_ltFn_x3f_2716_;
v___y_2627_ = v___y_2699_;
v___y_2628_ = v___y_2700_;
v___y_2629_ = v___y_2701_;
v___y_2630_ = v___y_2702_;
v___y_2631_ = v___y_2703_;
v___y_2632_ = v___y_2704_;
v___y_2633_ = v___y_2706_;
v___y_2634_ = v___y_2705_;
v___y_2635_ = v___y_2707_;
v___y_2636_ = v_a_2728_;
v___y_2637_ = v_a_2730_;
v___y_2638_ = v___y_2708_;
v___y_2639_ = v___y_2711_;
v___y_2640_ = v___y_2710_;
v___y_2641_ = v___y_2709_;
v___y_2642_ = v___y_2714_;
v___y_2643_ = v___y_2713_;
v_homomulFn_x3f_2644_ = v___y_2712_;
v___y_2645_ = v___y_2717_;
v___y_2646_ = v___y_2718_;
v___y_2647_ = v___y_2719_;
v___y_2648_ = v___y_2720_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v___y_2712_);
v_a_2731_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2729_);
v___x_2732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__8));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2732_, v_val_2602_, v_type_2519_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref(v___x_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__10));
v___x_2736_ = l_Lean_mkConst(v___x_2735_, v___y_2715_);
lean_inc_ref_n(v_type_2519_, 3);
v___x_2737_ = l_Lean_mkApp4(v___x_2736_, v_type_2519_, v_type_2519_, v_type_2519_, v_a_2734_);
v___x_2738_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2737_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___x_2738_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v_a_2739_);
v___x_2741_ = v___x_2604_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
v___y_2620_ = v___y_2693_;
v___y_2621_ = v___y_2694_;
v___y_2622_ = v___y_2695_;
v___y_2623_ = v___y_2696_;
v___y_2624_ = v___y_2697_;
v___y_2625_ = v___y_2698_;
v___y_2626_ = v_ltFn_x3f_2716_;
v___y_2627_ = v___y_2699_;
v___y_2628_ = v___y_2700_;
v___y_2629_ = v___y_2701_;
v___y_2630_ = v___y_2702_;
v___y_2631_ = v___y_2703_;
v___y_2632_ = v___y_2704_;
v___y_2633_ = v___y_2706_;
v___y_2634_ = v___y_2705_;
v___y_2635_ = v___y_2707_;
v___y_2636_ = v_a_2728_;
v___y_2637_ = v_a_2731_;
v___y_2638_ = v___y_2708_;
v___y_2639_ = v___y_2711_;
v___y_2640_ = v___y_2710_;
v___y_2641_ = v___y_2709_;
v___y_2642_ = v___y_2714_;
v___y_2643_ = v___y_2713_;
v_homomulFn_x3f_2644_ = v___x_2741_;
v___y_2645_ = v___y_2717_;
v___y_2646_ = v___y_2718_;
v___y_2647_ = v___y_2719_;
v___y_2648_ = v___y_2720_;
v___y_2649_ = v___y_2721_;
v___y_2650_ = v___y_2722_;
v___y_2651_ = v___y_2723_;
v___y_2652_ = v___y_2724_;
v___y_2653_ = v___y_2725_;
v___y_2654_ = v___y_2726_;
goto v___jp_2619_;
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2731_);
lean_dec_ref(v___y_2704_);
lean_dec(v_a_2728_);
lean_dec(v_ltFn_x3f_2716_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2743_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2738_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2738_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2731_);
lean_dec_ref(v___y_2704_);
lean_dec(v_a_2728_);
lean_dec(v_ltFn_x3f_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2751_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2733_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2733_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_a_2728_);
lean_dec(v_ltFn_x3f_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2759_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2729_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2729_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_ltFn_x3f_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2767_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2727_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2727_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
v___jp_2775_:
{
if (lean_obj_tag(v_a_2616_) == 1)
{
lean_object* v_val_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_val_2810_ = lean_ctor_get(v_a_2616_, 0);
v___x_2811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__12));
v___x_2812_ = l_Lean_mkConst(v___x_2811_, v___y_2791_);
lean_inc(v_val_2810_);
lean_inc_ref(v_type_2519_);
v___x_2813_ = l_Lean_mkAppB(v___x_2812_, v_type_2519_, v_val_2810_);
v___x_2814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2813_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 0, v_a_2815_);
v___x_2817_ = v___x_2609_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
v___y_2693_ = v___y_2776_;
v___y_2694_ = v___y_2777_;
v___y_2695_ = v___y_2778_;
v___y_2696_ = v___y_2779_;
v___y_2697_ = v___y_2780_;
v___y_2698_ = v___y_2781_;
v___y_2699_ = v___y_2782_;
v___y_2700_ = v___y_2783_;
v___y_2701_ = v___y_2784_;
v___y_2702_ = v___y_2785_;
v___y_2703_ = v___y_2786_;
v___y_2704_ = v___y_2787_;
v___y_2705_ = v___y_2789_;
v___y_2706_ = v___y_2788_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v_leFn_x3f_2799_;
v___y_2709_ = v___y_2794_;
v___y_2710_ = v___y_2793_;
v___y_2711_ = v___y_2792_;
v___y_2712_ = v___y_2797_;
v___y_2713_ = v___y_2796_;
v___y_2714_ = v___y_2795_;
v___y_2715_ = v___y_2798_;
v_ltFn_x3f_2716_ = v___x_2817_;
v___y_2717_ = v___y_2800_;
v___y_2718_ = v___y_2801_;
v___y_2719_ = v___y_2802_;
v___y_2720_ = v___y_2803_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_a_2616_);
lean_dec(v_leFn_x3f_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v_a_2618_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2819_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2814_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2814_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_dec(v___y_2791_);
lean_del_object(v___x_2609_);
lean_inc(v___y_2797_);
v___y_2693_ = v___y_2776_;
v___y_2694_ = v___y_2777_;
v___y_2695_ = v___y_2778_;
v___y_2696_ = v___y_2779_;
v___y_2697_ = v___y_2780_;
v___y_2698_ = v___y_2781_;
v___y_2699_ = v___y_2782_;
v___y_2700_ = v___y_2783_;
v___y_2701_ = v___y_2784_;
v___y_2702_ = v___y_2785_;
v___y_2703_ = v___y_2786_;
v___y_2704_ = v___y_2787_;
v___y_2705_ = v___y_2789_;
v___y_2706_ = v___y_2788_;
v___y_2707_ = v___y_2790_;
v___y_2708_ = v_leFn_x3f_2799_;
v___y_2709_ = v___y_2794_;
v___y_2710_ = v___y_2793_;
v___y_2711_ = v___y_2792_;
v___y_2712_ = v___y_2797_;
v___y_2713_ = v___y_2796_;
v___y_2714_ = v___y_2795_;
v___y_2715_ = v___y_2798_;
v_ltFn_x3f_2716_ = v___y_2797_;
v___y_2717_ = v___y_2800_;
v___y_2718_ = v___y_2801_;
v___y_2719_ = v___y_2802_;
v___y_2720_ = v___y_2803_;
v___y_2721_ = v___y_2804_;
v___y_2722_ = v___y_2805_;
v___y_2723_ = v___y_2806_;
v___y_2724_ = v___y_2807_;
v___y_2725_ = v___y_2808_;
v___y_2726_ = v___y_2809_;
goto v___jp_2692_;
}
}
v___jp_2827_:
{
lean_object* v___x_2860_; 
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2602_, v_type_2519_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2862_, v_val_2602_, v_type_2519_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_n(v_a_2864_, 2);
lean_dec_ref(v___x_2863_);
v___x_2865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16));
lean_inc(v___y_2841_);
v___x_2866_ = l_Lean_mkConst(v___x_2865_, v___y_2841_);
lean_inc_ref(v_type_2519_);
v___x_2867_ = l_Lean_mkAppB(v___x_2866_, v_type_2519_, v_a_2864_);
v___x_2868_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2867_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__18));
lean_inc(v___y_2841_);
v___x_2871_ = l_Lean_mkConst(v___x_2870_, v___y_2841_);
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__19);
lean_inc_ref(v_type_2519_);
v___x_2874_ = l_Lean_mkAppB(v___x_2871_, v_type_2519_, v___x_2873_);
v___x_2875_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2874_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_3097_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_3097_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_3097_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
if (lean_obj_tag(v_a_2876_) == 1)
{
lean_object* v_val_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_2878_);
v_val_2880_ = lean_ctor_get(v_a_2876_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_2882_ = v_a_2876_;
v_isShared_2883_ = v_isSharedCheck_3092_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_val_2880_);
lean_dec(v_a_2876_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_3092_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__21));
lean_inc(v___y_2841_);
v___x_2885_ = l_Lean_mkConst(v___x_2884_, v___y_2841_);
lean_inc_ref(v_type_2519_);
v___x_2886_ = l_Lean_mkApp3(v___x_2885_, v_type_2519_, v___x_2873_, v_val_2880_);
v___x_2887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2886_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_n(v_a_2888_, 2);
lean_dec_ref(v___x_2887_);
lean_inc(v_a_2869_);
v___x_2889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2869_, v_a_2888_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
lean_dec_ref(v___x_2889_);
v___x_2890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__23));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2890_, v_val_2602_, v_type_2519_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc_n(v_a_2892_, 2);
lean_dec_ref(v___x_2891_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__25));
lean_inc(v___y_2848_);
v___x_2894_ = l_Lean_mkConst(v___x_2893_, v___y_2848_);
lean_inc_ref_n(v_type_2519_, 3);
v___x_2895_ = l_Lean_mkApp4(v___x_2894_, v_type_2519_, v_type_2519_, v_type_2519_, v_a_2892_);
v___x_2896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2895_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__27));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2898_, v_val_2602_, v_type_2519_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc_n(v_a_2900_, 2);
lean_dec_ref(v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__29));
lean_inc(v___y_2841_);
v___x_2902_ = l_Lean_mkConst(v___x_2901_, v___y_2841_);
lean_inc_ref(v_type_2519_);
v___x_2903_ = l_Lean_mkAppB(v___x_2902_, v_type_2519_, v_a_2900_);
v___x_2904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2903_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref(v___x_2904_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2906_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2602_, v_type_2519_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_n(v_a_2907_, 2);
lean_dec_ref(v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___y_2835_);
v___x_2911_ = l_Lean_mkConst(v___x_2908_, v___x_2910_);
v___x_2912_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2519_, 2);
lean_inc_ref(v___x_2911_);
v___x_2913_ = l_Lean_mkApp4(v___x_2911_, v___x_2912_, v_type_2519_, v_type_2519_, v_a_2907_);
v___x_2914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2913_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2602_, v_type_2519_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_n(v_a_2917_, 2);
lean_dec_ref(v___x_2916_);
v___x_2918_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2519_, 2);
v___x_2919_ = l_Lean_mkApp4(v___x_2911_, v___x_2918_, v_type_2519_, v_type_2519_, v_a_2917_);
v___x_2920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2919_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__30));
v___x_2923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__31));
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2924_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___x_2922_, v___x_2923_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc_ref(v___y_2844_);
v___x_2925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2864_, v___y_2844_, v___x_2924_, v_val_2602_, v_type_2519_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref(v___x_2925_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__32));
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2927_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___x_2922_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__34));
v___x_2929_ = lean_box(0);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2832_, v___y_2844_, v___x_2927_, v___x_2928_, v_val_2602_, v_type_2519_, v___x_2929_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec_ref(v___x_2930_);
v___x_2931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__35));
lean_inc_ref(v___y_2839_);
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2932_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___y_2839_, v___x_2931_);
v___x_2933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__37));
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc_ref(v___y_2845_);
v___x_2934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2892_, v___y_2845_, v___x_2932_, v___x_2933_, v_val_2602_, v_type_2519_, v___x_2929_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec_ref(v___x_2934_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__38));
lean_inc_ref(v___y_2839_);
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2936_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___y_2839_, v___x_2935_);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
v___x_2937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2900_, v___y_2845_, v___x_2936_, v_val_2602_, v_type_2519_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v___x_2937_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__39));
lean_inc_ref(v___y_2842_);
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2939_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___y_2842_, v___x_2938_);
v___x_2940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__41));
v___x_2941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__42);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc_ref(v___y_2828_);
v___x_2942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2907_, v___y_2828_, v___x_2939_, v___x_2940_, v_val_2602_, v_type_2519_, v___x_2941_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_dec_ref(v___x_2942_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__43));
lean_inc_ref(v___y_2842_);
lean_inc_ref(v___y_2830_);
lean_inc_ref(v___y_2847_);
v___x_2944_ = l_Lean_Name_mkStr4(v___y_2847_, v___y_2830_, v___y_2842_, v___x_2943_);
v___x_2945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__44);
lean_inc_ref(v_type_2519_);
lean_inc(v_val_2602_);
lean_inc_ref(v___y_2828_);
v___x_2946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2917_, v___y_2828_, v___x_2944_, v___x_2940_, v_val_2602_, v_type_2519_, v___x_2945_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_dec_ref(v___x_2946_);
if (lean_obj_tag(v_a_2613_) == 1)
{
lean_object* v_val_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_val_2947_ = lean_ctor_get(v_a_2613_, 0);
v___x_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__46));
lean_inc(v___y_2841_);
v___x_2949_ = l_Lean_mkConst(v___x_2948_, v___y_2841_);
lean_inc(v_val_2947_);
lean_inc_ref(v_type_2519_);
v___x_2950_ = l_Lean_mkAppB(v___x_2949_, v_type_2519_, v_val_2947_);
v___x_2951_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2950_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v_a_2952_);
v___x_2954_ = v___x_2882_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2776_ = v___x_2872_;
v___y_2777_ = v_a_2897_;
v___y_2778_ = v___y_2828_;
v___y_2779_ = v___y_2829_;
v___y_2780_ = v_a_2921_;
v___y_2781_ = v___y_2831_;
v___y_2782_ = v___y_2833_;
v___y_2783_ = v___y_2834_;
v___y_2784_ = v_a_2888_;
v___y_2785_ = v_a_2905_;
v___y_2786_ = v_a_2915_;
v___y_2787_ = v___y_2836_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2837_;
v___y_2790_ = v___y_2840_;
v___y_2791_ = v___y_2841_;
v___y_2792_ = v___y_2843_;
v___y_2793_ = v_a_2861_;
v___y_2794_ = v_charInst_x3f_2849_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v_a_2869_;
v___y_2797_ = v___x_2929_;
v___y_2798_ = v___y_2848_;
v_leFn_x3f_2799_ = v___x_2954_;
v___y_2800_ = v___y_2850_;
v___y_2801_ = v___y_2851_;
v___y_2802_ = v___y_2852_;
v___y_2803_ = v___y_2853_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
goto v___jp_2775_;
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2921_);
lean_dec(v_a_2915_);
lean_dec(v_a_2905_);
lean_dec(v_a_2897_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2956_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2951_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2951_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_del_object(v___x_2882_);
v___y_2776_ = v___x_2872_;
v___y_2777_ = v_a_2897_;
v___y_2778_ = v___y_2828_;
v___y_2779_ = v___y_2829_;
v___y_2780_ = v_a_2921_;
v___y_2781_ = v___y_2831_;
v___y_2782_ = v___y_2833_;
v___y_2783_ = v___y_2834_;
v___y_2784_ = v_a_2888_;
v___y_2785_ = v_a_2905_;
v___y_2786_ = v_a_2915_;
v___y_2787_ = v___y_2836_;
v___y_2788_ = v___y_2838_;
v___y_2789_ = v___y_2837_;
v___y_2790_ = v___y_2840_;
v___y_2791_ = v___y_2841_;
v___y_2792_ = v___y_2843_;
v___y_2793_ = v_a_2861_;
v___y_2794_ = v_charInst_x3f_2849_;
v___y_2795_ = v___y_2846_;
v___y_2796_ = v_a_2869_;
v___y_2797_ = v___x_2929_;
v___y_2798_ = v___y_2848_;
v_leFn_x3f_2799_ = v___x_2929_;
v___y_2800_ = v___y_2850_;
v___y_2801_ = v___y_2851_;
v___y_2802_ = v___y_2852_;
v___y_2803_ = v___y_2853_;
v___y_2804_ = v___y_2854_;
v___y_2805_ = v___y_2855_;
v___y_2806_ = v___y_2856_;
v___y_2807_ = v___y_2857_;
v___y_2808_ = v___y_2858_;
v___y_2809_ = v___y_2859_;
goto v___jp_2775_;
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2915_);
lean_dec(v_a_2905_);
lean_dec(v_a_2897_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2964_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2946_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2946_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2905_);
lean_dec(v_a_2897_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2972_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2942_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2942_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2897_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2980_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2937_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2937_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2988_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2934_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2934_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_2996_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2930_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2930_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3004_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2925_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2925_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v_a_2917_);
lean_dec(v_a_2915_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3012_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_2920_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_2920_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_2915_);
lean_dec_ref(v___x_2911_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3020_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_2916_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_2916_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v___x_2911_);
lean_dec(v_a_2907_);
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3028_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2914_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2914_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_2905_);
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3036_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2906_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2906_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_2900_);
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3044_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2904_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2904_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec(v_a_2897_);
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3052_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2899_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2899_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v_a_2892_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3060_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2896_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_2896_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3068_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2891_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2891_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_2888_);
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3076_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2889_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2889_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_del_object(v___x_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3084_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2887_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2887_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
lean_dec(v_a_2876_);
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v___x_3093_ = lean_box(0);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_3093_);
v___x_3095_ = v___x_2878_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_2869_);
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3098_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2875_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_2875_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_2864_);
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3106_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_2868_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_2868_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_2861_);
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3114_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_2863_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_2863_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_charInst_x3f_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2618_);
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3122_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_2860_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_2860_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec(v_a_2616_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3485_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_2617_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_2617_);
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
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_a_2613_);
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3493_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_2615_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_2615_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_del_object(v___x_2609_);
lean_dec(v_a_2607_);
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
v_a_3501_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_2612_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_2612_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_del_object(v___x_2604_);
lean_dec(v_val_2602_);
lean_dec_ref(v_type_2519_);
return v___x_2606_;
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec(v_a_2598_);
lean_dec_ref(v_type_2519_);
v___x_3511_ = lean_box(0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_3511_);
v___x_3513_ = v___x_2600_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v_type_2519_);
v_a_3516_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_2597_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_2597_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2532_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
v___jp_2535_:
{
if (lean_obj_tag(v___y_2537_) == 0)
{
lean_dec_ref(v___y_2537_);
v___y_2532_ = v___y_2536_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2536_);
v_a_2538_ = lean_ctor_get(v___y_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___y_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___y_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___y_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
v___jp_2546_:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2556_, v___y_2557_, v___y_2553_, v___y_2548_, v___y_2551_, v___y_2558_, v___y_2552_, v___y_2549_, v___y_2555_, v___y_2554_, v___y_2547_, v___y_2550_, v___y_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2561_, v___y_2553_, v___y_2548_);
v___y_2536_ = v___y_2553_;
v___y_2537_ = v___x_2562_;
goto v___jp_2535_;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v___y_2553_);
v_a_2563_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2560_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2560_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
v___jp_2571_:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2581_, v___y_2582_, v___y_2578_, v___y_2573_, v___y_2576_, v___y_2583_, v___y_2577_, v___y_2574_, v___y_2580_, v___y_2579_, v___y_2572_, v___y_2575_, v___y_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_n(v_a_2586_, 2);
lean_dec_ref(v___x_2585_);
v___x_2587_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2586_, v___y_2578_, v___y_2573_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref(v___x_2587_);
v___x_2588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2586_, v___y_2578_, v___y_2573_);
v___y_2536_ = v___y_2578_;
v___y_2537_ = v___x_2588_;
goto v___jp_2535_;
}
else
{
lean_dec(v_a_2586_);
v___y_2536_ = v___y_2578_;
v___y_2537_ = v___x_2587_;
goto v___jp_2535_;
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v___y_2578_);
v_a_2589_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2585_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b2_3537_, lean_object* v_x_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_x_3538_, v_x_3539_, v_x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3542_, lean_object* v_x_3543_, size_t v_x_3544_, size_t v_x_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg(v_x_3543_, v_x_3544_, v_x_3545_, v_x_3546_, v_x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_){
_start:
{
size_t v_x_577779__boxed_3555_; size_t v_x_577780__boxed_3556_; lean_object* v_res_3557_; 
v_x_577779__boxed_3555_ = lean_unbox_usize(v_x_3551_);
lean_dec(v_x_3551_);
v_x_577780__boxed_3556_ = lean_unbox_usize(v_x_3552_);
lean_dec(v_x_3552_);
v_res_3557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0(v_00_u03b2_3549_, v_x_3550_, v_x_577779__boxed_3555_, v_x_577780__boxed_3556_, v_x_3553_, v_x_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3558_, lean_object* v_n_3559_, lean_object* v_k_3560_, lean_object* v_v_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1___redArg(v_n_3559_, v_k_3560_, v_v_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3563_, size_t v_depth_3564_, lean_object* v_keys_3565_, lean_object* v_vals_3566_, lean_object* v_heq_3567_, lean_object* v_i_3568_, lean_object* v_entries_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3564_, v_keys_3565_, v_vals_3566_, v_i_3568_, v_entries_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_depth_3572_, lean_object* v_keys_3573_, lean_object* v_vals_3574_, lean_object* v_heq_3575_, lean_object* v_i_3576_, lean_object* v_entries_3577_){
_start:
{
size_t v_depth_boxed_3578_; lean_object* v_res_3579_; 
v_depth_boxed_3578_ = lean_unbox_usize(v_depth_3572_);
lean_dec(v_depth_3572_);
v_res_3579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3571_, v_depth_boxed_3578_, v_keys_3573_, v_vals_3574_, v_heq_3575_, v_i_3576_, v_entries_3577_);
lean_dec_ref(v_vals_3574_);
lean_dec_ref(v_keys_3573_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3581_, v_x_3582_, v_x_3583_, v_x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_3586_, lean_object* v_a_3587_, lean_object* v_s_3588_){
_start:
{
lean_object* v_structs_3589_; lean_object* v_typeIdOf_3590_; lean_object* v_exprToStructId_3591_; lean_object* v_exprToStructIdEntries_3592_; lean_object* v_forbiddenNatModules_3593_; lean_object* v_natStructs_3594_; lean_object* v_natTypeIdOf_3595_; lean_object* v_exprToNatStructId_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
v_structs_3589_ = lean_ctor_get(v_s_3588_, 0);
v_typeIdOf_3590_ = lean_ctor_get(v_s_3588_, 1);
v_exprToStructId_3591_ = lean_ctor_get(v_s_3588_, 2);
v_exprToStructIdEntries_3592_ = lean_ctor_get(v_s_3588_, 3);
v_forbiddenNatModules_3593_ = lean_ctor_get(v_s_3588_, 4);
v_natStructs_3594_ = lean_ctor_get(v_s_3588_, 5);
v_natTypeIdOf_3595_ = lean_ctor_get(v_s_3588_, 6);
v_exprToNatStructId_3596_ = lean_ctor_get(v_s_3588_, 7);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_s_3588_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3598_ = v_s_3588_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_exprToNatStructId_3596_);
lean_inc(v_natTypeIdOf_3595_);
lean_inc(v_natStructs_3594_);
lean_inc(v_forbiddenNatModules_3593_);
lean_inc(v_exprToStructIdEntries_3592_);
lean_inc(v_exprToStructId_3591_);
lean_inc(v_typeIdOf_3590_);
lean_inc(v_structs_3589_);
lean_dec(v_s_3588_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_typeIdOf_3590_, v_type_3586_, v_a_3587_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_structs_3589_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_exprToStructId_3591_);
lean_ctor_set(v_reuseFailAlloc_3603_, 3, v_exprToStructIdEntries_3592_);
lean_ctor_set(v_reuseFailAlloc_3603_, 4, v_forbiddenNatModules_3593_);
lean_ctor_set(v_reuseFailAlloc_3603_, 5, v_natStructs_3594_);
lean_ctor_set(v_reuseFailAlloc_3603_, 6, v_natTypeIdOf_3595_);
lean_ctor_set(v_reuseFailAlloc_3603_, 7, v_exprToNatStructId_3596_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3605_, lean_object* v_vals_3606_, lean_object* v_i_3607_, lean_object* v_k_3608_){
_start:
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = lean_array_get_size(v_keys_3605_);
v___x_3610_ = lean_nat_dec_lt(v_i_3607_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec(v_i_3607_);
v___x_3611_ = lean_box(0);
return v___x_3611_;
}
else
{
lean_object* v_k_x27_3612_; uint8_t v___x_3613_; 
v_k_x27_3612_ = lean_array_fget_borrowed(v_keys_3605_, v_i_3607_);
v___x_3613_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_3608_, v_k_x27_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3615_ = lean_nat_add(v_i_3607_, v___x_3614_);
lean_dec(v_i_3607_);
v_i_3607_ = v___x_3615_;
goto _start;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = lean_array_fget_borrowed(v_vals_3606_, v_i_3607_);
lean_dec(v_i_3607_);
lean_inc(v___x_3617_);
v___x_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3619_, lean_object* v_vals_3620_, lean_object* v_i_3621_, lean_object* v_k_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3619_, v_vals_3620_, v_i_3621_, v_k_3622_);
lean_dec_ref(v_k_3622_);
lean_dec_ref(v_vals_3620_);
lean_dec_ref(v_keys_3619_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_3624_, size_t v_x_3625_, lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3624_) == 0)
{
lean_object* v_es_3627_; lean_object* v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; size_t v___x_3631_; lean_object* v_j_3632_; lean_object* v___x_3633_; 
v_es_3627_ = lean_ctor_get(v_x_3624_, 0);
v___x_3628_ = lean_box(2);
v___x_3629_ = ((size_t)5ULL);
v___x_3630_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_3631_ = lean_usize_land(v_x_3625_, v___x_3630_);
v_j_3632_ = lean_usize_to_nat(v___x_3631_);
v___x_3633_ = lean_array_get_borrowed(v___x_3628_, v_es_3627_, v_j_3632_);
lean_dec(v_j_3632_);
switch(lean_obj_tag(v___x_3633_))
{
case 0:
{
lean_object* v_key_3634_; lean_object* v_val_3635_; uint8_t v___x_3636_; 
v_key_3634_ = lean_ctor_get(v___x_3633_, 0);
v_val_3635_ = lean_ctor_get(v___x_3633_, 1);
v___x_3636_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3626_, v_key_3634_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_box(0);
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; 
lean_inc(v_val_3635_);
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_val_3635_);
return v___x_3638_;
}
}
case 1:
{
lean_object* v_node_3639_; size_t v___x_3640_; 
v_node_3639_ = lean_ctor_get(v___x_3633_, 0);
v___x_3640_ = lean_usize_shift_right(v_x_3625_, v___x_3629_);
v_x_3624_ = v_node_3639_;
v_x_3625_ = v___x_3640_;
goto _start;
}
default: 
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_box(0);
return v___x_3642_;
}
}
}
else
{
lean_object* v_ks_3643_; lean_object* v_vs_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_ks_3643_ = lean_ctor_get(v_x_3624_, 0);
v_vs_3644_ = lean_ctor_get(v_x_3624_, 1);
v___x_3645_ = lean_unsigned_to_nat(0u);
v___x_3646_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3643_, v_vs_3644_, v___x_3645_, v_x_3626_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
size_t v_x_7996__boxed_3650_; lean_object* v_res_3651_; 
v_x_7996__boxed_3650_ = lean_unbox_usize(v_x_3648_);
lean_dec(v_x_3648_);
v_res_3651_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3647_, v_x_7996__boxed_3650_, v_x_3649_);
lean_dec_ref(v_x_3649_);
lean_dec_ref(v_x_3647_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_3652_, lean_object* v_x_3653_){
_start:
{
uint64_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3653_);
v___x_3655_ = lean_uint64_to_usize(v___x_3654_);
v___x_3656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3652_, v___x_3655_, v_x_3653_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_3657_, lean_object* v_x_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_3657_, v_x_3658_);
lean_dec_ref(v_x_3658_);
lean_dec_ref(v_x_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3663_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3742_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3742_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3742_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
uint8_t v_linarith_3677_; 
v_linarith_3677_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*12 + 22);
lean_dec(v_a_3673_);
if (v_linarith_3677_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_dec_ref(v_type_3660_);
v___x_3678_ = lean_box(0);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3678_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v___x_3682_; 
lean_del_object(v___x_3675_);
lean_inc_ref(v_type_3660_);
v___x_3682_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3733_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3733_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3733_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint8_t v___x_3687_; 
v___x_3687_ = lean_unbox(v_a_3683_);
lean_dec(v_a_3683_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; 
lean_del_object(v___x_3685_);
v___x_3688_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3661_, v_a_3669_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3720_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3720_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3720_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_typeIdOf_3693_; lean_object* v___x_3694_; 
v_typeIdOf_3693_ = lean_ctor_get(v_a_3689_, 1);
lean_inc_ref(v_typeIdOf_3693_);
lean_dec(v_a_3689_);
v___x_3694_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_3693_, v_type_3660_);
lean_dec_ref(v_typeIdOf_3693_);
if (lean_obj_tag(v___x_3694_) == 1)
{
lean_object* v_val_3695_; lean_object* v___x_3697_; 
lean_dec_ref(v_type_3660_);
v_val_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_val_3695_);
lean_dec_ref(v___x_3694_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v_val_3695_);
v___x_3697_ = v___x_3691_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_val_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
else
{
lean_object* v___x_3699_; 
lean_dec(v___x_3694_);
lean_del_object(v___x_3691_);
lean_inc_ref(v_type_3660_);
v___x_3699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc_n(v_a_3700_, 2);
lean_dec_ref(v___x_3699_);
v___f_3701_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_3701_, 0, v_type_3660_);
lean_closure_set(v___f_3701_, 1, v_a_3700_);
v___x_3702_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3703_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3702_, v___f_3701_, v_a_3661_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v___x_3703_, 0);
lean_dec(v_unused_3711_);
v___x_3705_ = v___x_3703_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_dec(v___x_3703_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v_a_3700_);
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3700_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_a_3700_);
v_a_3712_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3703_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3703_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_dec_ref(v_type_3660_);
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v_type_3660_);
v_a_3721_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3688_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3688_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_dec_ref(v_type_3660_);
v___x_3729_ = lean_box(0);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3729_);
v___x_3731_ = v___x_3685_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_type_3660_);
v_a_3734_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3682_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3682_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_type_3660_);
v_a_3743_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3672_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3672_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
lean_dec(v_a_3753_);
lean_dec(v_a_3752_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_3764_, lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_3765_, v_x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_3768_, lean_object* v_x_3769_, lean_object* v_x_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_3768_, v_x_3769_, v_x_3770_);
lean_dec_ref(v_x_3770_);
lean_dec_ref(v_x_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3772_, lean_object* v_x_3773_, size_t v_x_3774_, lean_object* v_x_3775_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_3773_, v_x_3774_, v_x_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3777_, lean_object* v_x_3778_, lean_object* v_x_3779_, lean_object* v_x_3780_){
_start:
{
size_t v_x_8224__boxed_3781_; lean_object* v_res_3782_; 
v_x_8224__boxed_3781_ = lean_unbox_usize(v_x_3779_);
lean_dec(v_x_3779_);
v_res_3782_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_3777_, v_x_3778_, v_x_8224__boxed_3781_, v_x_3780_);
lean_dec_ref(v_x_3780_);
lean_dec_ref(v_x_3778_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3783_, lean_object* v_keys_3784_, lean_object* v_vals_3785_, lean_object* v_heq_3786_, lean_object* v_i_3787_, lean_object* v_k_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3784_, v_vals_3785_, v_i_3787_, v_k_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3790_, lean_object* v_keys_3791_, lean_object* v_vals_3792_, lean_object* v_heq_3793_, lean_object* v_i_3794_, lean_object* v_k_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3790_, v_keys_3791_, v_vals_3792_, v_heq_3793_, v_i_3794_, v_k_3795_);
lean_dec_ref(v_k_3795_);
lean_dec_ref(v_vals_3792_);
lean_dec_ref(v_keys_3791_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_3797_, lean_object* v_type_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_3805_ = lean_box(0);
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v_u_3797_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_Lean_mkConst(v___x_3804_, v___x_3806_);
v___x_3808_ = l_Lean_Expr_app___override(v___x_3807_, v_type_3798_);
v___x_3809_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_3808_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_3810_, lean_object* v_type_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_3810_, v_type_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_3818_, lean_object* v_type_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_3818_, v_type_3819_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_3832_, lean_object* v_type_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_3832_, v_type_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec(v_a_3834_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_3846_, lean_object* v_s_3847_){
_start:
{
lean_object* v_structs_3848_; lean_object* v_typeIdOf_3849_; lean_object* v_exprToStructId_3850_; lean_object* v_exprToStructIdEntries_3851_; lean_object* v_forbiddenNatModules_3852_; lean_object* v_natStructs_3853_; lean_object* v_natTypeIdOf_3854_; lean_object* v_exprToNatStructId_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3863_; 
v_structs_3848_ = lean_ctor_get(v_s_3847_, 0);
v_typeIdOf_3849_ = lean_ctor_get(v_s_3847_, 1);
v_exprToStructId_3850_ = lean_ctor_get(v_s_3847_, 2);
v_exprToStructIdEntries_3851_ = lean_ctor_get(v_s_3847_, 3);
v_forbiddenNatModules_3852_ = lean_ctor_get(v_s_3847_, 4);
v_natStructs_3853_ = lean_ctor_get(v_s_3847_, 5);
v_natTypeIdOf_3854_ = lean_ctor_get(v_s_3847_, 6);
v_exprToNatStructId_3855_ = lean_ctor_get(v_s_3847_, 7);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_s_3847_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3857_ = v_s_3847_;
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_exprToNatStructId_3855_);
lean_inc(v_natTypeIdOf_3854_);
lean_inc(v_natStructs_3853_);
lean_inc(v_forbiddenNatModules_3852_);
lean_inc(v_exprToStructIdEntries_3851_);
lean_inc(v_exprToStructId_3850_);
lean_inc(v_typeIdOf_3849_);
lean_inc(v_structs_3848_);
lean_dec(v_s_3847_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_array_push(v_natStructs_3853_, v___x_3846_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 5, v___x_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_structs_3848_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_typeIdOf_3849_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_exprToStructId_3850_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_exprToStructIdEntries_3851_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_forbiddenNatModules_3852_);
lean_ctor_set(v_reuseFailAlloc_3862_, 5, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3862_, 6, v_natTypeIdOf_3854_);
lean_ctor_set(v_reuseFailAlloc_3862_, 7, v_exprToNatStructId_3855_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_ref_3870_; lean_object* v___x_3871_; lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3880_; 
v_ref_3870_ = lean_ctor_get(v___y_3867_, 5);
v___x_3871_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
lean_inc(v_ref_3870_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_ref_3870_);
lean_ctor_set(v___x_3876_, 1, v_a_3872_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 1);
lean_ctor_set(v___x_3874_, 0, v___x_3876_);
v___x_3878_ = v___x_3874_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
return v_res_3887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12(void){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__12);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
return v___x_3918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__14));
v___x_3921_ = l_Lean_stringToMessageData(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v___x_3934_; 
lean_inc_ref(v_type_3922_);
v___x_3934_ = l_Lean_Meta_getDecLevel(v_type_3922_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc_n(v_a_3935_, 2);
lean_dec_ref(v___x_3934_);
lean_inc_ref(v_type_3922_);
v___x_3936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_3935_, v_type_3922_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_4229_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_3939_ = v___x_3936_;
v_isShared_3940_ = v_isSharedCheck_4229_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3936_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_4229_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
if (lean_obj_tag(v_a_3937_) == 1)
{
lean_object* v_val_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_del_object(v___x_3939_);
v_val_3941_ = lean_ctor_get(v_a_3937_, 0);
lean_inc_n(v_val_3941_, 2);
lean_dec_ref(v_a_3937_);
v___x_3942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__2));
v___x_3943_ = lean_box(0);
lean_inc(v_a_3935_);
v___x_3944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3944_, 0, v_a_3935_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
lean_inc_ref(v___x_3944_);
v___x_3945_ = l_Lean_mkConst(v___x_3942_, v___x_3944_);
lean_inc_ref(v_type_3922_);
v___x_3946_ = l_Lean_mkAppB(v___x_3945_, v_type_3922_, v_val_3941_);
v___x_3947_ = l_Lean_Meta_Sym_canon(v___x_3946_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref(v___x_3947_);
v___x_3949_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3948_, v_a_3928_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc_n(v_a_3950_, 2);
lean_dec_ref(v___x_3949_);
v___x_3951_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_3950_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
if (lean_obj_tag(v_a_3952_) == 1)
{
lean_object* v_val_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_4204_; 
v_val_3953_ = lean_ctor_get(v_a_3952_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_a_3952_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_3955_ = v_a_3952_;
v_isShared_3956_ = v_isSharedCheck_4204_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_val_3953_);
lean_dec(v_a_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_4204_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3957_, v_a_3935_, v_type_3922_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref(v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__3));
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3960_, v_a_3935_, v_type_3922_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
lean_inc(v_a_3959_);
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3963_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(v_a_3935_, v_type_3922_, v_a_3959_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3963_);
lean_inc(v_a_3959_);
lean_inc(v_a_3962_);
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3965_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(v_a_3935_, v_type_3922_, v_a_3962_, v_a_3959_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
lean_inc(v_a_3959_);
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3967_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(v_a_3935_, v_type_3922_, v_a_3959_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref(v___x_3967_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__62));
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_3970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3969_, v_a_3935_, v_type_3922_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_n(v_a_3971_, 2);
lean_dec_ref(v___x_3970_);
v___x_3972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__64));
lean_inc_ref(v___x_3944_);
lean_inc_n(v_a_3935_, 2);
v___x_3973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_a_3935_);
lean_ctor_set(v___x_3973_, 1, v___x_3944_);
lean_inc_ref(v___x_3973_);
v___x_3974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3974_, 0, v_a_3935_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_mkConst(v___x_3972_, v___x_3974_);
lean_inc_ref_n(v_type_3922_, 3);
v___x_3976_ = l_Lean_mkApp4(v___x_3975_, v_type_3922_, v_type_3922_, v_type_3922_, v_a_3971_);
v___x_3977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3976_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v_orderedAddInst_x3f_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___x_3977_);
if (lean_obj_tag(v_a_3959_) == 1)
{
if (lean_obj_tag(v_a_3964_) == 1)
{
lean_object* v_val_4133_; lean_object* v_val_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v_val_4133_ = lean_ctor_get(v_a_3959_, 0);
v_val_4134_ = lean_ctor_get(v_a_3964_, 0);
v___x_4135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__66));
lean_inc_ref(v___x_3944_);
v___x_4136_ = l_Lean_mkConst(v___x_4135_, v___x_3944_);
lean_inc(v_val_4134_);
lean_inc(v_val_4133_);
lean_inc_ref(v_type_3922_);
v___x_4137_ = l_Lean_mkApp4(v___x_4136_, v_type_3922_, v_a_3971_, v_val_4133_, v_val_4134_);
v___x_4138_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_4137_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v___x_4138_);
v_orderedAddInst_x3f_3980_ = v_a_4139_;
v___y_3981_ = v_a_3923_;
v___y_3982_ = v_a_3924_;
v___y_3983_ = v_a_3925_;
v___y_3984_ = v_a_3926_;
v___y_3985_ = v_a_3927_;
v___y_3986_ = v_a_3928_;
v___y_3987_ = v_a_3929_;
v___y_3988_ = v_a_3930_;
v___y_3989_ = v_a_3931_;
v___y_3990_ = v_a_3932_;
goto v___jp_3979_;
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_a_3964_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3962_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4140_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4138_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4138_);
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
else
{
lean_dec(v_a_3971_);
v___y_4122_ = v_a_3923_;
v___y_4123_ = v_a_3924_;
v___y_4124_ = v_a_3925_;
v___y_4125_ = v_a_3926_;
v___y_4126_ = v_a_3927_;
v___y_4127_ = v_a_3928_;
v___y_4128_ = v_a_3929_;
v___y_4129_ = v_a_3930_;
v___y_4130_ = v_a_3931_;
v___y_4131_ = v_a_3932_;
goto v___jp_4121_;
}
}
else
{
lean_dec(v_a_3971_);
v___y_4122_ = v_a_3923_;
v___y_4123_ = v_a_3924_;
v___y_4124_ = v_a_3925_;
v___y_4125_ = v_a_3926_;
v___y_4126_ = v_a_3927_;
v___y_4127_ = v_a_3928_;
v___y_4128_ = v_a_3929_;
v___y_4129_ = v_a_3930_;
v___y_4130_ = v_a_3931_;
v___y_4131_ = v_a_3932_;
goto v___jp_4121_;
}
v___jp_3979_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc_ref(v___x_3944_);
v___x_3992_ = l_Lean_mkConst(v___x_3991_, v___x_3944_);
lean_inc_ref(v_type_3922_);
v___x_3993_ = l_Lean_Expr_app___override(v___x_3992_, v_type_3922_);
v___x_3994_ = l_Lean_Meta_Sym_synthInstance(v___x_3993_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref(v___x_3994_);
v___x_3996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
lean_inc_ref(v___x_3944_);
v___x_3997_ = l_Lean_mkConst(v___x_3996_, v___x_3944_);
lean_inc_ref(v_type_3922_);
v___x_3998_ = l_Lean_mkAppB(v___x_3997_, v_type_3922_, v_a_3995_);
v___x_3999_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_3998_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__8));
lean_inc_ref(v___x_3944_);
v___x_4002_ = l_Lean_mkConst(v___x_4001_, v___x_3944_);
lean_inc(v_val_3941_);
lean_inc_ref(v_type_3922_);
v___x_4003_ = l_Lean_mkAppB(v___x_4002_, v_type_3922_, v_val_3941_);
v___x_4004_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4003_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref(v___x_4004_);
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__14));
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_4007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4006_, v_a_3935_, v_type_3922_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__16));
v___x_4010_ = l_Lean_mkConst(v___x_4009_, v___x_3944_);
lean_inc_ref(v_type_3922_);
v___x_4011_ = l_Lean_mkAppB(v___x_4010_, v_type_3922_, v_a_4008_);
v___x_4012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4011_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4014_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_4012_);
lean_inc_ref(v_type_3922_);
lean_inc(v_a_3935_);
v___x_4014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_3935_, v_type_3922_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref(v___x_4014_);
v___x_4016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4017_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___x_3973_);
v___x_4019_ = l_Lean_mkConst(v___x_4016_, v___x_4018_);
v___x_4020_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_3922_, 2);
v___x_4021_ = l_Lean_mkApp4(v___x_4019_, v___x_4020_, v_type_3922_, v_type_3922_, v_a_4015_);
v___x_4022_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4021_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref(v___x_4022_);
v___x_4024_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3981_, v___y_3989_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v_natStructs_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___f_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v_natStructs_4026_ = lean_ctor_get(v_a_4025_, 5);
lean_inc_ref(v_natStructs_4026_);
lean_dec(v_a_4025_);
v___x_4027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__11));
lean_inc(v_a_3935_);
v___x_4028_ = l_Lean_Level_succ___override(v_a_3935_);
v___x_4029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
lean_ctor_set(v___x_4029_, 1, v___x_3943_);
v___x_4030_ = l_Lean_mkConst(v___x_4027_, v___x_4029_);
v___x_4031_ = l_Lean_Expr_app___override(v___x_4030_, v_a_3950_);
v___x_4032_ = lean_array_get_size(v_natStructs_4026_);
lean_dec_ref(v_natStructs_4026_);
v___x_4033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__13);
v___x_4034_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4032_);
lean_ctor_set(v___x_4034_, 1, v_val_3953_);
lean_ctor_set(v___x_4034_, 2, v_type_3922_);
lean_ctor_set(v___x_4034_, 3, v_a_3935_);
lean_ctor_set(v___x_4034_, 4, v_val_3941_);
lean_ctor_set(v___x_4034_, 5, v_a_3959_);
lean_ctor_set(v___x_4034_, 6, v_a_3962_);
lean_ctor_set(v___x_4034_, 7, v_a_3966_);
lean_ctor_set(v___x_4034_, 8, v_a_3964_);
lean_ctor_set(v___x_4034_, 9, v_orderedAddInst_x3f_3980_);
lean_ctor_set(v___x_4034_, 10, v_a_3968_);
lean_ctor_set(v___x_4034_, 11, v_a_4000_);
lean_ctor_set(v___x_4034_, 12, v___x_4031_);
lean_ctor_set(v___x_4034_, 13, v_a_4013_);
lean_ctor_set(v___x_4034_, 14, v_a_4005_);
lean_ctor_set(v___x_4034_, 15, v_a_3978_);
lean_ctor_set(v___x_4034_, 16, v_a_4023_);
lean_ctor_set(v___x_4034_, 17, v___x_4033_);
v___f_4035_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4035_, 0, v___x_4034_);
v___x_4036_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4037_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4036_, v___f_4035_, v___y_3981_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4047_; 
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; 
v_unused_4048_ = lean_ctor_get(v___x_4037_, 0);
lean_dec(v_unused_4048_);
v___x_4039_ = v___x_4037_;
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
else
{
lean_dec(v___x_4037_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4047_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_4032_);
v___x_4042_ = v___x_3955_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4032_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4042_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_del_object(v___x_3955_);
v_a_4049_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4037_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4037_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_4023_);
lean_dec(v_a_4013_);
lean_dec(v_a_4005_);
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4057_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4024_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4024_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_a_4013_);
lean_dec(v_a_4005_);
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4065_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4022_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4022_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_4013_);
lean_dec(v_a_4005_);
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4073_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4014_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4014_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4005_);
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4081_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4012_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4012_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_a_4005_);
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4089_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4007_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4007_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4000_);
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4097_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4004_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4004_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4105_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_3999_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_3999_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_orderedAddInst_x3f_3980_);
lean_dec(v_a_3978_);
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4113_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_3994_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_3994_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
v___jp_4121_:
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_box(0);
v_orderedAddInst_x3f_3980_ = v___x_4132_;
v___y_3981_ = v___y_4122_;
v___y_3982_ = v___y_4123_;
v___y_3983_ = v___y_4124_;
v___y_3984_ = v___y_4125_;
v___y_3985_ = v___y_4126_;
v___y_3986_ = v___y_4127_;
v___y_3987_ = v___y_4128_;
v___y_3988_ = v___y_4129_;
v___y_3989_ = v___y_4130_;
v___y_3990_ = v___y_4131_;
goto v___jp_3979_;
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v___x_3973_);
lean_dec(v_a_3971_);
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4148_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_3977_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_3977_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_a_3968_);
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4156_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_3970_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_3970_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_a_3966_);
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4164_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_3967_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_3967_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_a_3964_);
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4172_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_3965_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_3965_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec(v_a_3962_);
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4180_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_3963_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_3963_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec(v_a_3959_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4188_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_3961_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_3961_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4196_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_3958_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_3958_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec(v_a_3952_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v___x_4205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__15);
v___x_4206_ = l_Lean_indentExpr(v_a_3950_);
v___x_4207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_4207_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_4208_;
}
}
else
{
lean_dec(v_a_3950_);
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
return v___x_3951_;
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4209_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_3949_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_3949_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v___x_3944_);
lean_dec(v_val_3941_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4217_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_3947_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_3947_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4227_; 
lean_dec(v_a_3937_);
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v___x_4225_ = lean_box(0);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_4225_);
v___x_4227_ = v___x_3939_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_type_3922_);
v_a_4230_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_3936_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_3936_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v_type_3922_);
v_a_4238_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_3934_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_3934_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec(v_a_4247_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_4259_, lean_object* v_msg_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4260_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_4273_, lean_object* v_msg_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_4273_, v_msg_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec(v___y_4275_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_4287_, lean_object* v_a_4288_, lean_object* v_s_4289_){
_start:
{
lean_object* v_structs_4290_; lean_object* v_typeIdOf_4291_; lean_object* v_exprToStructId_4292_; lean_object* v_exprToStructIdEntries_4293_; lean_object* v_forbiddenNatModules_4294_; lean_object* v_natStructs_4295_; lean_object* v_natTypeIdOf_4296_; lean_object* v_exprToNatStructId_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4305_; 
v_structs_4290_ = lean_ctor_get(v_s_4289_, 0);
v_typeIdOf_4291_ = lean_ctor_get(v_s_4289_, 1);
v_exprToStructId_4292_ = lean_ctor_get(v_s_4289_, 2);
v_exprToStructIdEntries_4293_ = lean_ctor_get(v_s_4289_, 3);
v_forbiddenNatModules_4294_ = lean_ctor_get(v_s_4289_, 4);
v_natStructs_4295_ = lean_ctor_get(v_s_4289_, 5);
v_natTypeIdOf_4296_ = lean_ctor_get(v_s_4289_, 6);
v_exprToNatStructId_4297_ = lean_ctor_get(v_s_4289_, 7);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_s_4289_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4299_ = v_s_4289_;
v_isShared_4300_ = v_isSharedCheck_4305_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_exprToNatStructId_4297_);
lean_inc(v_natTypeIdOf_4296_);
lean_inc(v_natStructs_4295_);
lean_inc(v_forbiddenNatModules_4294_);
lean_inc(v_exprToStructIdEntries_4293_);
lean_inc(v_exprToStructId_4292_);
lean_inc(v_typeIdOf_4291_);
lean_inc(v_structs_4290_);
lean_dec(v_s_4289_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4305_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
v___x_4301_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0___redArg(v_natTypeIdOf_4296_, v_type_4287_, v_a_4288_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 6, v___x_4301_);
v___x_4303_ = v___x_4299_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_structs_4290_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_typeIdOf_4291_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v_exprToStructId_4292_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v_exprToStructIdEntries_4293_);
lean_ctor_set(v_reuseFailAlloc_4304_, 4, v_forbiddenNatModules_4294_);
lean_ctor_set(v_reuseFailAlloc_4304_, 5, v_natStructs_4295_);
lean_ctor_set(v_reuseFailAlloc_4304_, 6, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4304_, 7, v_exprToNatStructId_4297_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4306_, lean_object* v_i_4307_, lean_object* v_k_4308_){
_start:
{
lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4309_ = lean_array_get_size(v_keys_4306_);
v___x_4310_ = lean_nat_dec_lt(v_i_4307_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_dec(v_i_4307_);
return v___x_4310_;
}
else
{
lean_object* v_k_x27_4311_; uint8_t v___x_4312_; 
v_k_x27_4311_ = lean_array_fget_borrowed(v_keys_4306_, v_i_4307_);
v___x_4312_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_4308_, v_k_x27_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_unsigned_to_nat(1u);
v___x_4314_ = lean_nat_add(v_i_4307_, v___x_4313_);
lean_dec(v_i_4307_);
v_i_4307_ = v___x_4314_;
goto _start;
}
else
{
lean_dec(v_i_4307_);
return v___x_4312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4316_, lean_object* v_i_4317_, lean_object* v_k_4318_){
_start:
{
uint8_t v_res_4319_; lean_object* v_r_4320_; 
v_res_4319_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4316_, v_i_4317_, v_k_4318_);
lean_dec_ref(v_k_4318_);
lean_dec_ref(v_keys_4316_);
v_r_4320_ = lean_box(v_res_4319_);
return v_r_4320_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4321_, size_t v_x_4322_, lean_object* v_x_4323_){
_start:
{
if (lean_obj_tag(v_x_4321_) == 0)
{
lean_object* v_es_4324_; lean_object* v___x_4325_; size_t v___x_4326_; size_t v___x_4327_; size_t v___x_4328_; lean_object* v_j_4329_; lean_object* v___x_4330_; 
v_es_4324_ = lean_ctor_get(v_x_4321_, 0);
v___x_4325_ = lean_box(2);
v___x_4326_ = ((size_t)5ULL);
v___x_4327_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f_spec__0_spec__0___redArg___closed__1);
v___x_4328_ = lean_usize_land(v_x_4322_, v___x_4327_);
v_j_4329_ = lean_usize_to_nat(v___x_4328_);
v___x_4330_ = lean_array_get_borrowed(v___x_4325_, v_es_4324_, v_j_4329_);
lean_dec(v_j_4329_);
switch(lean_obj_tag(v___x_4330_))
{
case 0:
{
lean_object* v_key_4331_; uint8_t v___x_4332_; 
v_key_4331_ = lean_ctor_get(v___x_4330_, 0);
v___x_4332_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4323_, v_key_4331_);
return v___x_4332_;
}
case 1:
{
lean_object* v_node_4333_; size_t v___x_4334_; 
v_node_4333_ = lean_ctor_get(v___x_4330_, 0);
v___x_4334_ = lean_usize_shift_right(v_x_4322_, v___x_4326_);
v_x_4321_ = v_node_4333_;
v_x_4322_ = v___x_4334_;
goto _start;
}
default: 
{
uint8_t v___x_4336_; 
v___x_4336_ = 0;
return v___x_4336_;
}
}
}
else
{
lean_object* v_ks_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_ks_4337_ = lean_ctor_get(v_x_4321_, 0);
v___x_4338_ = lean_unsigned_to_nat(0u);
v___x_4339_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4337_, v___x_4338_, v_x_4323_);
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v_x_4342_){
_start:
{
size_t v_x_10574__boxed_4343_; uint8_t v_res_4344_; lean_object* v_r_4345_; 
v_x_10574__boxed_4343_ = lean_unbox_usize(v_x_4341_);
lean_dec(v_x_4341_);
v_res_4344_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4340_, v_x_10574__boxed_4343_, v_x_4342_);
lean_dec_ref(v_x_4342_);
lean_dec_ref(v_x_4340_);
v_r_4345_ = lean_box(v_res_4344_);
return v_r_4345_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_4346_, lean_object* v_x_4347_){
_start:
{
uint64_t v___x_4348_; size_t v___x_4349_; uint8_t v___x_4350_; 
v___x_4348_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4347_);
v___x_4349_ = lean_uint64_to_usize(v___x_4348_);
v___x_4350_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4346_, v___x_4349_, v_x_4347_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4351_, lean_object* v_x_4352_){
_start:
{
uint8_t v_res_4353_; lean_object* v_r_4354_; 
v_res_4353_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_4351_, v_x_4352_);
lean_dec_ref(v_x_4352_);
lean_dec_ref(v_x_4351_);
v_r_4354_ = lean_box(v_res_4353_);
return v_r_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4358_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4457_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4457_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4457_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
uint8_t v_linarith_4372_; 
v_linarith_4372_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*12 + 22);
lean_dec(v_a_4368_);
if (v_linarith_4372_ == 0)
{
lean_object* v___x_4373_; lean_object* v___x_4375_; 
lean_dec_ref(v_type_4355_);
v___x_4373_ = lean_box(0);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4373_);
v___x_4375_ = v___x_4370_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
else
{
lean_object* v___x_4377_; 
lean_del_object(v___x_4370_);
v___x_4377_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4356_, v_a_4364_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4448_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4448_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4448_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_forbiddenNatModules_4382_; uint8_t v___x_4383_; 
v_forbiddenNatModules_4382_ = lean_ctor_get(v_a_4378_, 4);
lean_inc_ref(v_forbiddenNatModules_4382_);
lean_dec(v_a_4378_);
v___x_4383_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_4382_, v_type_4355_);
lean_dec_ref(v_forbiddenNatModules_4382_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_del_object(v___x_4380_);
lean_inc_ref(v_type_4355_);
v___x_4384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4435_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4435_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4435_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___x_4389_; 
v___x_4389_ = lean_unbox(v_a_4385_);
lean_dec(v_a_4385_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; 
lean_del_object(v___x_4387_);
v___x_4390_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4356_, v_a_4364_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4422_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4422_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4422_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v_natTypeIdOf_4395_; lean_object* v___x_4396_; 
v_natTypeIdOf_4395_ = lean_ctor_get(v_a_4391_, 6);
lean_inc_ref(v_natTypeIdOf_4395_);
lean_dec(v_a_4391_);
v___x_4396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_4395_, v_type_4355_);
lean_dec_ref(v_natTypeIdOf_4395_);
if (lean_obj_tag(v___x_4396_) == 1)
{
lean_object* v_val_4397_; lean_object* v___x_4399_; 
lean_dec_ref(v_type_4355_);
v_val_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_val_4397_);
lean_dec_ref(v___x_4396_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v_val_4397_);
v___x_4399_ = v___x_4393_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_val_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
else
{
lean_object* v___x_4401_; 
lean_dec(v___x_4396_);
lean_del_object(v___x_4393_);
lean_inc_ref(v_type_4355_);
v___x_4401_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___f_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_n(v_a_4402_, 2);
lean_dec_ref(v___x_4401_);
v___f_4403_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4403_, 0, v_type_4355_);
lean_closure_set(v___f_4403_, 1, v_a_4402_);
v___x_4404_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4404_, v___f_4403_, v_a_4356_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4405_, 0);
lean_dec(v_unused_4413_);
v___x_4407_ = v___x_4405_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v___x_4405_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v_a_4402_);
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4402_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v_a_4402_);
v_a_4414_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4405_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4405_);
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
lean_dec_ref(v_type_4355_);
return v___x_4401_;
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec_ref(v_type_4355_);
v_a_4423_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4390_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4390_);
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
lean_object* v___x_4431_; lean_object* v___x_4433_; 
lean_dec_ref(v_type_4355_);
v___x_4431_ = lean_box(0);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4431_);
v___x_4433_ = v___x_4387_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec_ref(v_type_4355_);
v_a_4436_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4384_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4384_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v___x_4444_; lean_object* v___x_4446_; 
lean_dec_ref(v_type_4355_);
v___x_4444_ = lean_box(0);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4444_);
v___x_4446_ = v___x_4380_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec_ref(v_type_4355_);
v_a_4449_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4377_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4377_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref(v_type_4355_);
v_a_4458_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4367_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4367_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec(v_a_4467_);
return v_res_4478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_4479_, lean_object* v_x_4480_, lean_object* v_x_4481_){
_start:
{
uint8_t v___x_4482_; 
v___x_4482_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_4480_, v_x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4483_, lean_object* v_x_4484_, lean_object* v_x_4485_){
_start:
{
uint8_t v_res_4486_; lean_object* v_r_4487_; 
v_res_4486_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_4483_, v_x_4484_, v_x_4485_);
lean_dec_ref(v_x_4485_);
lean_dec_ref(v_x_4484_);
v_r_4487_ = lean_box(v_res_4486_);
return v_r_4487_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4488_, lean_object* v_x_4489_, size_t v_x_4490_, lean_object* v_x_4491_){
_start:
{
uint8_t v___x_4492_; 
v___x_4492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_4489_, v_x_4490_, v_x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_){
_start:
{
size_t v_x_10834__boxed_4497_; uint8_t v_res_4498_; lean_object* v_r_4499_; 
v_x_10834__boxed_4497_ = lean_unbox_usize(v_x_4495_);
lean_dec(v_x_4495_);
v_res_4498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_4493_, v_x_4494_, v_x_10834__boxed_4497_, v_x_4496_);
lean_dec_ref(v_x_4496_);
lean_dec_ref(v_x_4494_);
v_r_4499_ = lean_box(v_res_4498_);
return v_r_4499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4500_, lean_object* v_keys_4501_, lean_object* v_vals_4502_, lean_object* v_heq_4503_, lean_object* v_i_4504_, lean_object* v_k_4505_){
_start:
{
uint8_t v___x_4506_; 
v___x_4506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4501_, v_i_4504_, v_k_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4507_, lean_object* v_keys_4508_, lean_object* v_vals_4509_, lean_object* v_heq_4510_, lean_object* v_i_4511_, lean_object* v_k_4512_){
_start:
{
uint8_t v_res_4513_; lean_object* v_r_4514_; 
v_res_4513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4507_, v_keys_4508_, v_vals_4509_, v_heq_4510_, v_i_4511_, v_k_4512_);
lean_dec_ref(v_k_4512_);
lean_dec_ref(v_vals_4509_);
lean_dec_ref(v_keys_4508_);
v_r_4514_ = lean_box(v_res_4513_);
return v_r_4514_;
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
