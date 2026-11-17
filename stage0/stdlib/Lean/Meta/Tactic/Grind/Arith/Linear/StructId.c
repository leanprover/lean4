// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Sym.Arith.Insts import Init.Grind.Module.Envelope import Lean.CoreM
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind` unexpected failure, failure to initialize auxiliary `IntModule`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6;
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
lean_object* v___x_228_; lean_object* v_env_229_; uint8_t v___x_230_; lean_object* v_env_231_; lean_object* v___x_232_; lean_object* v_toCold_233_; lean_object* v_mctx_234_; lean_object* v_lctx_235_; lean_object* v_options_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = 0;
v_env_231_ = l_Lean_Environment_setRecordingDeps(v_env_229_, v___x_230_);
v___x_232_ = lean_st_ref_get(v___y_224_);
v_toCold_233_ = lean_ctor_get(v___y_225_, 0);
v_mctx_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_mctx_234_);
lean_dec(v___x_232_);
v_lctx_235_ = lean_ctor_get(v___y_223_, 2);
v_options_236_ = lean_ctor_get(v_toCold_233_, 2);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_lctx_235_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_231_);
lean_ctor_set(v___x_237_, 1, v_mctx_234_);
lean_ctor_set(v___x_237_, 2, v_lctx_235_);
lean_ctor_set(v___x_237_, 3, v_options_236_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_222_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0___boxed(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msgData_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_ref_253_ = lean_ctor_get(v___y_250_, 2);
v___x_254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_ref_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_ref_253_);
lean_ctor_set(v___x_259_, 1, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(lean_object* v_a_271_, lean_object* v_b_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
lean_inc_ref(v_b_272_);
lean_inc_ref(v_a_271_);
v___x_278_ = l_Lean_Meta_isDefEqD(v_a_271_, v_b_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_291_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_291_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = lean_unbox(v_a_279_);
lean_dec(v_a_279_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v_a_285_; lean_object* v___x_286_; 
lean_del_object(v___x_281_);
v___x_284_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_271_, v_b_272_);
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_a_285_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec_ref(v_b_272_);
lean_dec_ref(v_a_271_);
v___x_287_ = lean_box(0);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_287_);
v___x_289_ = v___x_281_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_b_272_);
lean_dec_ref(v_a_271_);
v_a_292_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_278_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_278_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq___boxed(lean_object* v_a_300_, lean_object* v_b_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_300_, v_b_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(lean_object* v_00_u03b1_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___redArg(v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0___boxed(lean_object* v_00_u03b1_316_, lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0(v_00_u03b1_316_, v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(lean_object* v_p_324_, lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v_x_327_, size_t v_x_328_, size_t v_x_329_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v_cs_330_; size_t v_j_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_cs_330_ = lean_ctor_get(v_x_327_, 0);
v_j_331_ = lean_usize_shift_right(v_x_328_, v_x_329_);
v___x_332_ = lean_usize_to_nat(v_j_331_);
v___x_333_ = lean_array_get_size(v_cs_330_);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec(v___x_332_);
lean_dec(v_p_324_);
return v_x_327_;
}
else
{
lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_352_; 
lean_inc_ref(v_cs_330_);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_x_327_, 0);
lean_dec(v_unused_353_);
v___x_336_ = v_x_327_;
v_isShared_337_ = v_isSharedCheck_352_;
goto v_resetjp_335_;
}
else
{
lean_dec(v_x_327_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_352_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v_i_341_; size_t v___x_342_; size_t v_shift_343_; lean_object* v_v_344_; lean_object* v___x_345_; lean_object* v_xs_x27_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_shift_left(v___x_338_, v_x_329_);
v___x_340_ = lean_usize_sub(v___x_339_, v___x_338_);
v_i_341_ = lean_usize_land(v_x_328_, v___x_340_);
v___x_342_ = ((size_t)5ULL);
v_shift_343_ = lean_usize_sub(v_x_329_, v___x_342_);
v_v_344_ = lean_array_fget(v_cs_330_, v___x_332_);
v___x_345_ = lean_box(0);
v_xs_x27_346_ = lean_array_fset(v_cs_330_, v___x_332_, v___x_345_);
v___x_347_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_324_, v___x_325_, v___x_326_, v_v_344_, v_i_341_, v_shift_343_);
v___x_348_ = lean_array_fset(v_xs_x27_346_, v___x_332_, v___x_347_);
lean_dec(v___x_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_348_);
v___x_350_ = v___x_336_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_vs_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_vs_354_ = lean_ctor_get(v_x_327_, 0);
v___x_355_ = lean_usize_to_nat(v_x_328_);
v___x_356_ = lean_array_get_size(v_vs_354_);
v___x_357_ = lean_nat_dec_lt(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v___x_355_);
lean_dec(v_p_324_);
return v_x_327_;
}
else
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_372_; 
lean_inc_ref(v_vs_354_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_327_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v_x_327_, 0);
lean_dec(v_unused_373_);
v___x_359_ = v_x_327_;
v_isShared_360_ = v_isSharedCheck_372_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_x_327_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_372_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
uint8_t v___x_361_; lean_object* v_v_362_; lean_object* v___x_363_; lean_object* v_xs_x27_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_361_ = lean_nat_dec_lt(v___x_325_, v___x_326_);
v_v_362_ = lean_array_fget(v_vs_354_, v___x_355_);
v___x_363_ = lean_box(0);
v_xs_x27_364_ = lean_array_fset(v_vs_354_, v___x_355_, v___x_363_);
v___x_365_ = lean_box(9);
v___x_366_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_366_, 0, v_p_324_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*2, v___x_361_);
v___x_367_ = l_Lean_PersistentArray_push___redArg(v_v_362_, v___x_366_);
v___x_368_ = lean_array_fset(v_xs_x27_364_, v___x_355_, v___x_367_);
lean_dec(v___x_355_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_368_);
v___x_370_ = v___x_359_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0___boxed(lean_object* v_p_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
size_t v_x_283__boxed_380_; size_t v_x_284__boxed_381_; lean_object* v_res_382_; 
v_x_283__boxed_380_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_x_284__boxed_381_ = lean_unbox_usize(v_x_379_);
lean_dec(v_x_379_);
v_res_382_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_374_, v___x_375_, v___x_376_, v_x_377_, v_x_283__boxed_380_, v_x_284__boxed_381_);
lean_dec(v___x_376_);
lean_dec(v___x_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(lean_object* v_p_383_, lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v_t_386_, lean_object* v_i_387_){
_start:
{
lean_object* v_root_388_; lean_object* v_tail_389_; lean_object* v_size_390_; size_t v_shift_391_; lean_object* v_tailOff_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_419_; 
v_root_388_ = lean_ctor_get(v_t_386_, 0);
v_tail_389_ = lean_ctor_get(v_t_386_, 1);
v_size_390_ = lean_ctor_get(v_t_386_, 2);
v_shift_391_ = lean_ctor_get_usize(v_t_386_, 4);
v_tailOff_392_ = lean_ctor_get(v_t_386_, 3);
v_isSharedCheck_419_ = !lean_is_exclusive(v_t_386_);
if (v_isSharedCheck_419_ == 0)
{
v___x_394_ = v_t_386_;
v_isShared_395_ = v_isSharedCheck_419_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_tailOff_392_);
lean_inc(v_size_390_);
lean_inc(v_tail_389_);
lean_inc(v_root_388_);
lean_dec(v_t_386_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_419_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___x_396_; 
v___x_396_ = lean_nat_dec_le(v_tailOff_392_, v_i_387_);
if (v___x_396_ == 0)
{
size_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_usize_of_nat(v_i_387_);
v___x_398_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0_spec__0(v_p_383_, v___x_384_, v___x_385_, v_root_388_, v___x_397_, v_shift_391_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_398_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_tail_389_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_size_390_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_tailOff_392_);
lean_ctor_set_usize(v_reuseFailAlloc_401_, 4, v_shift_391_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_nat_sub(v_i_387_, v_tailOff_392_);
v___x_403_ = lean_array_get_size(v_tail_389_);
v___x_404_ = lean_nat_dec_lt(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v___x_402_);
lean_dec(v_p_383_);
if (v_isShared_395_ == 0)
{
v___x_406_ = v___x_394_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_root_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_tail_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_size_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_tailOff_392_);
lean_ctor_set_usize(v_reuseFailAlloc_407_, 4, v_shift_391_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
uint8_t v___x_408_; lean_object* v_v_409_; lean_object* v___x_410_; lean_object* v_xs_x27_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_408_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
v_v_409_ = lean_array_fget(v_tail_389_, v___x_402_);
v___x_410_ = lean_box(0);
v_xs_x27_411_ = lean_array_fset(v_tail_389_, v___x_402_, v___x_410_);
v___x_412_ = lean_box(9);
v___x_413_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_413_, 0, v_p_383_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*2, v___x_408_);
v___x_414_ = l_Lean_PersistentArray_push___redArg(v_v_409_, v___x_413_);
v___x_415_ = lean_array_fset(v_xs_x27_411_, v___x_402_, v___x_414_);
lean_dec(v___x_402_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_415_);
v___x_417_ = v___x_394_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_root_388_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_size_390_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_tailOff_392_);
lean_ctor_set_usize(v_reuseFailAlloc_418_, 4, v_shift_391_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0___boxed(lean_object* v_p_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v_t_423_, lean_object* v_i_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_420_, v___x_421_, v___x_422_, v_t_423_, v_i_424_);
lean_dec(v_i_424_);
lean_dec(v___x_422_);
lean_dec(v___x_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(lean_object* v_a_426_, lean_object* v_p_427_, lean_object* v_one_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_structs_430_; lean_object* v_typeIdOf_431_; lean_object* v_exprToStructId_432_; lean_object* v_exprToStructIdEntries_433_; lean_object* v_forbiddenNatModules_434_; lean_object* v_natStructs_435_; lean_object* v_natTypeIdOf_436_; lean_object* v_exprToNatStructId_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_structs_430_ = lean_ctor_get(v_s_429_, 0);
v_typeIdOf_431_ = lean_ctor_get(v_s_429_, 1);
v_exprToStructId_432_ = lean_ctor_get(v_s_429_, 2);
v_exprToStructIdEntries_433_ = lean_ctor_get(v_s_429_, 3);
v_forbiddenNatModules_434_ = lean_ctor_get(v_s_429_, 4);
v_natStructs_435_ = lean_ctor_get(v_s_429_, 5);
v_natTypeIdOf_436_ = lean_ctor_get(v_s_429_, 6);
v_exprToNatStructId_437_ = lean_ctor_get(v_s_429_, 7);
v___x_438_ = lean_array_get_size(v_structs_430_);
v___x_439_ = lean_nat_dec_lt(v_a_426_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v_p_427_);
return v_s_429_;
}
else
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_exprToNatStructId_437_);
lean_inc_ref(v_natTypeIdOf_436_);
lean_inc_ref(v_natStructs_435_);
lean_inc_ref(v_forbiddenNatModules_434_);
lean_inc_ref(v_exprToStructIdEntries_433_);
lean_inc_ref(v_exprToStructId_432_);
lean_inc_ref(v_typeIdOf_431_);
lean_inc_ref(v_structs_430_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_s_429_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; lean_object* v_unused_506_; lean_object* v_unused_507_; lean_object* v_unused_508_; lean_object* v_unused_509_; 
v_unused_502_ = lean_ctor_get(v_s_429_, 7);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_s_429_, 6);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_s_429_, 5);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_s_429_, 4);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_s_429_, 3);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_s_429_, 2);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_s_429_, 1);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_s_429_, 0);
lean_dec(v_unused_509_);
v___x_441_ = v_s_429_;
v_isShared_442_ = v_isSharedCheck_501_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_s_429_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_501_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_v_443_; lean_object* v_id_444_; lean_object* v_ringId_x3f_445_; lean_object* v_type_446_; lean_object* v_u_447_; lean_object* v_intModuleInst_448_; lean_object* v_leInst_x3f_449_; lean_object* v_ltInst_x3f_450_; lean_object* v_lawfulOrderLTInst_x3f_451_; lean_object* v_isPreorderInst_x3f_452_; lean_object* v_orderedAddInst_x3f_453_; lean_object* v_isLinearInst_x3f_454_; lean_object* v_noNatDivInst_x3f_455_; lean_object* v_ringInst_x3f_456_; lean_object* v_commRingInst_x3f_457_; lean_object* v_orderedRingInst_x3f_458_; lean_object* v_fieldInst_x3f_459_; lean_object* v_charInst_x3f_460_; lean_object* v_zero_461_; lean_object* v_ofNatZero_462_; lean_object* v_one_x3f_463_; lean_object* v_leFn_x3f_464_; lean_object* v_ltFn_x3f_465_; lean_object* v_addFn_466_; lean_object* v_zsmulFn_467_; lean_object* v_nsmulFn_468_; lean_object* v_zsmulFn_x3f_469_; lean_object* v_nsmulFn_x3f_470_; lean_object* v_homomulFn_x3f_471_; lean_object* v_subFn_472_; lean_object* v_negFn_473_; lean_object* v_vars_474_; lean_object* v_varMap_475_; lean_object* v_lowers_476_; lean_object* v_uppers_477_; lean_object* v_diseqs_478_; lean_object* v_assignment_479_; uint8_t v_caseSplits_480_; lean_object* v_conflict_x3f_481_; lean_object* v_diseqSplits_482_; lean_object* v_elimEqs_483_; lean_object* v_elimStack_484_; lean_object* v_occurs_485_; lean_object* v_ignored_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_500_; 
v_v_443_ = lean_array_fget(v_structs_430_, v_a_426_);
v_id_444_ = lean_ctor_get(v_v_443_, 0);
v_ringId_x3f_445_ = lean_ctor_get(v_v_443_, 1);
v_type_446_ = lean_ctor_get(v_v_443_, 2);
v_u_447_ = lean_ctor_get(v_v_443_, 3);
v_intModuleInst_448_ = lean_ctor_get(v_v_443_, 4);
v_leInst_x3f_449_ = lean_ctor_get(v_v_443_, 5);
v_ltInst_x3f_450_ = lean_ctor_get(v_v_443_, 6);
v_lawfulOrderLTInst_x3f_451_ = lean_ctor_get(v_v_443_, 7);
v_isPreorderInst_x3f_452_ = lean_ctor_get(v_v_443_, 8);
v_orderedAddInst_x3f_453_ = lean_ctor_get(v_v_443_, 9);
v_isLinearInst_x3f_454_ = lean_ctor_get(v_v_443_, 10);
v_noNatDivInst_x3f_455_ = lean_ctor_get(v_v_443_, 11);
v_ringInst_x3f_456_ = lean_ctor_get(v_v_443_, 12);
v_commRingInst_x3f_457_ = lean_ctor_get(v_v_443_, 13);
v_orderedRingInst_x3f_458_ = lean_ctor_get(v_v_443_, 14);
v_fieldInst_x3f_459_ = lean_ctor_get(v_v_443_, 15);
v_charInst_x3f_460_ = lean_ctor_get(v_v_443_, 16);
v_zero_461_ = lean_ctor_get(v_v_443_, 17);
v_ofNatZero_462_ = lean_ctor_get(v_v_443_, 18);
v_one_x3f_463_ = lean_ctor_get(v_v_443_, 19);
v_leFn_x3f_464_ = lean_ctor_get(v_v_443_, 20);
v_ltFn_x3f_465_ = lean_ctor_get(v_v_443_, 21);
v_addFn_466_ = lean_ctor_get(v_v_443_, 22);
v_zsmulFn_467_ = lean_ctor_get(v_v_443_, 23);
v_nsmulFn_468_ = lean_ctor_get(v_v_443_, 24);
v_zsmulFn_x3f_469_ = lean_ctor_get(v_v_443_, 25);
v_nsmulFn_x3f_470_ = lean_ctor_get(v_v_443_, 26);
v_homomulFn_x3f_471_ = lean_ctor_get(v_v_443_, 27);
v_subFn_472_ = lean_ctor_get(v_v_443_, 28);
v_negFn_473_ = lean_ctor_get(v_v_443_, 29);
v_vars_474_ = lean_ctor_get(v_v_443_, 30);
v_varMap_475_ = lean_ctor_get(v_v_443_, 31);
v_lowers_476_ = lean_ctor_get(v_v_443_, 32);
v_uppers_477_ = lean_ctor_get(v_v_443_, 33);
v_diseqs_478_ = lean_ctor_get(v_v_443_, 34);
v_assignment_479_ = lean_ctor_get(v_v_443_, 35);
v_caseSplits_480_ = lean_ctor_get_uint8(v_v_443_, sizeof(void*)*42);
v_conflict_x3f_481_ = lean_ctor_get(v_v_443_, 36);
v_diseqSplits_482_ = lean_ctor_get(v_v_443_, 37);
v_elimEqs_483_ = lean_ctor_get(v_v_443_, 38);
v_elimStack_484_ = lean_ctor_get(v_v_443_, 39);
v_occurs_485_ = lean_ctor_get(v_v_443_, 40);
v_ignored_486_ = lean_ctor_get(v_v_443_, 41);
v_isSharedCheck_500_ = !lean_is_exclusive(v_v_443_);
if (v_isSharedCheck_500_ == 0)
{
v___x_488_ = v_v_443_;
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_ignored_486_);
lean_inc(v_occurs_485_);
lean_inc(v_elimStack_484_);
lean_inc(v_elimEqs_483_);
lean_inc(v_diseqSplits_482_);
lean_inc(v_conflict_x3f_481_);
lean_inc(v_assignment_479_);
lean_inc(v_diseqs_478_);
lean_inc(v_uppers_477_);
lean_inc(v_lowers_476_);
lean_inc(v_varMap_475_);
lean_inc(v_vars_474_);
lean_inc(v_negFn_473_);
lean_inc(v_subFn_472_);
lean_inc(v_homomulFn_x3f_471_);
lean_inc(v_nsmulFn_x3f_470_);
lean_inc(v_zsmulFn_x3f_469_);
lean_inc(v_nsmulFn_468_);
lean_inc(v_zsmulFn_467_);
lean_inc(v_addFn_466_);
lean_inc(v_ltFn_x3f_465_);
lean_inc(v_leFn_x3f_464_);
lean_inc(v_one_x3f_463_);
lean_inc(v_ofNatZero_462_);
lean_inc(v_zero_461_);
lean_inc(v_charInst_x3f_460_);
lean_inc(v_fieldInst_x3f_459_);
lean_inc(v_orderedRingInst_x3f_458_);
lean_inc(v_commRingInst_x3f_457_);
lean_inc(v_ringInst_x3f_456_);
lean_inc(v_noNatDivInst_x3f_455_);
lean_inc(v_isLinearInst_x3f_454_);
lean_inc(v_orderedAddInst_x3f_453_);
lean_inc(v_isPreorderInst_x3f_452_);
lean_inc(v_lawfulOrderLTInst_x3f_451_);
lean_inc(v_ltInst_x3f_450_);
lean_inc(v_leInst_x3f_449_);
lean_inc(v_intModuleInst_448_);
lean_inc(v_u_447_);
lean_inc(v_type_446_);
lean_inc(v_ringId_x3f_445_);
lean_inc(v_id_444_);
lean_dec(v_v_443_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_500_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v_xs_x27_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_490_ = lean_box(0);
v_xs_x27_491_ = lean_array_fset(v_structs_430_, v_a_426_, v___x_490_);
v___x_492_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne_spec__0(v_p_427_, v_a_426_, v___x_438_, v_lowers_476_, v_one_428_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 32, v___x_492_);
v___x_494_ = v___x_488_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_id_444_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_ringId_x3f_445_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_type_446_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_u_447_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_intModuleInst_448_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_leInst_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_ltInst_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_lawfulOrderLTInst_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_isPreorderInst_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_499_, 9, v_orderedAddInst_x3f_453_);
lean_ctor_set(v_reuseFailAlloc_499_, 10, v_isLinearInst_x3f_454_);
lean_ctor_set(v_reuseFailAlloc_499_, 11, v_noNatDivInst_x3f_455_);
lean_ctor_set(v_reuseFailAlloc_499_, 12, v_ringInst_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_499_, 13, v_commRingInst_x3f_457_);
lean_ctor_set(v_reuseFailAlloc_499_, 14, v_orderedRingInst_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_499_, 15, v_fieldInst_x3f_459_);
lean_ctor_set(v_reuseFailAlloc_499_, 16, v_charInst_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_499_, 17, v_zero_461_);
lean_ctor_set(v_reuseFailAlloc_499_, 18, v_ofNatZero_462_);
lean_ctor_set(v_reuseFailAlloc_499_, 19, v_one_x3f_463_);
lean_ctor_set(v_reuseFailAlloc_499_, 20, v_leFn_x3f_464_);
lean_ctor_set(v_reuseFailAlloc_499_, 21, v_ltFn_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_499_, 22, v_addFn_466_);
lean_ctor_set(v_reuseFailAlloc_499_, 23, v_zsmulFn_467_);
lean_ctor_set(v_reuseFailAlloc_499_, 24, v_nsmulFn_468_);
lean_ctor_set(v_reuseFailAlloc_499_, 25, v_zsmulFn_x3f_469_);
lean_ctor_set(v_reuseFailAlloc_499_, 26, v_nsmulFn_x3f_470_);
lean_ctor_set(v_reuseFailAlloc_499_, 27, v_homomulFn_x3f_471_);
lean_ctor_set(v_reuseFailAlloc_499_, 28, v_subFn_472_);
lean_ctor_set(v_reuseFailAlloc_499_, 29, v_negFn_473_);
lean_ctor_set(v_reuseFailAlloc_499_, 30, v_vars_474_);
lean_ctor_set(v_reuseFailAlloc_499_, 31, v_varMap_475_);
lean_ctor_set(v_reuseFailAlloc_499_, 32, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_499_, 33, v_uppers_477_);
lean_ctor_set(v_reuseFailAlloc_499_, 34, v_diseqs_478_);
lean_ctor_set(v_reuseFailAlloc_499_, 35, v_assignment_479_);
lean_ctor_set(v_reuseFailAlloc_499_, 36, v_conflict_x3f_481_);
lean_ctor_set(v_reuseFailAlloc_499_, 37, v_diseqSplits_482_);
lean_ctor_set(v_reuseFailAlloc_499_, 38, v_elimEqs_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 39, v_elimStack_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 40, v_occurs_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 41, v_ignored_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*42, v_caseSplits_480_);
v___x_494_ = v_reuseFailAlloc_499_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_array_fset(v_xs_x27_491_, v_a_426_, v___x_494_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_495_);
v___x_497_ = v___x_441_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_typeIdOf_431_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_exprToStructId_432_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_exprToStructIdEntries_433_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_forbiddenNatModules_434_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_natStructs_435_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_natTypeIdOf_436_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_exprToNatStructId_437_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed(lean_object* v_a_510_, lean_object* v_p_511_, lean_object* v_one_512_, lean_object* v_s_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0(v_a_510_, v_p_511_, v_one_512_, v_s_513_);
lean_dec(v_one_512_);
lean_dec(v_a_510_);
return v_res_514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_to_int(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_518_ = lean_int_neg(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(lean_object* v_one_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_p_525_; lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__1);
v___x_524_ = lean_box(0);
lean_inc(v_one_519_);
v_p_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_525_, 0, v___x_523_);
lean_ctor_set(v_p_525_, 1, v_one_519_);
lean_ctor_set(v_p_525_, 2, v___x_524_);
lean_inc(v_a_520_);
v___f_526_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_526_, 0, v_a_520_);
lean_closure_set(v___f_526_, 1, v_p_525_);
lean_closure_set(v___f_526_, 2, v_one_519_);
v___x_527_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_528_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_527_, v___f_526_, v_a_521_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___boxed(lean_object* v_one_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec(v_a_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(lean_object* v_one_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_one_534_, v_a_535_, v_a_536_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___boxed(lean_object* v_one_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne(v_one_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec(v_a_550_);
lean_dec(v_a_549_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(lean_object* v_p_562_, lean_object* v_x_563_, size_t v_x_564_, size_t v_x_565_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_cs_566_; size_t v_j_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_cs_566_ = lean_ctor_get(v_x_563_, 0);
v_j_567_ = lean_usize_shift_right(v_x_564_, v_x_565_);
v___x_568_ = lean_usize_to_nat(v_j_567_);
v___x_569_ = lean_array_get_size(v_cs_566_);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v___x_568_);
lean_dec(v_p_562_);
return v_x_563_;
}
else
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_588_; 
lean_inc_ref(v_cs_566_);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_x_563_, 0);
lean_dec(v_unused_589_);
v___x_572_ = v_x_563_;
v_isShared_573_ = v_isSharedCheck_588_;
goto v_resetjp_571_;
}
else
{
lean_dec(v_x_563_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_588_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v_i_577_; size_t v___x_578_; size_t v_shift_579_; lean_object* v_v_580_; lean_object* v___x_581_; lean_object* v_xs_x27_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_shift_left(v___x_574_, v_x_565_);
v___x_576_ = lean_usize_sub(v___x_575_, v___x_574_);
v_i_577_ = lean_usize_land(v_x_564_, v___x_576_);
v___x_578_ = ((size_t)5ULL);
v_shift_579_ = lean_usize_sub(v_x_565_, v___x_578_);
v_v_580_ = lean_array_fget(v_cs_566_, v___x_568_);
v___x_581_ = lean_box(0);
v_xs_x27_582_ = lean_array_fset(v_cs_566_, v___x_568_, v___x_581_);
v___x_583_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_562_, v_v_580_, v_i_577_, v_shift_579_);
v___x_584_ = lean_array_fset(v_xs_x27_582_, v___x_568_, v___x_583_);
lean_dec(v___x_568_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_584_);
v___x_586_ = v___x_572_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_vs_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_vs_590_ = lean_ctor_get(v_x_563_, 0);
v___x_591_ = lean_usize_to_nat(v_x_564_);
v___x_592_ = lean_array_get_size(v_vs_590_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v___x_591_);
lean_dec(v_p_562_);
return v_x_563_;
}
else
{
lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_607_; 
lean_inc_ref(v_vs_590_);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_x_563_, 0);
lean_dec(v_unused_608_);
v___x_595_ = v_x_563_;
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
else
{
lean_dec(v_x_563_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_607_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_v_597_; lean_object* v___x_598_; lean_object* v_xs_x27_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_v_597_ = lean_array_fget(v_vs_590_, v___x_591_);
v___x_598_ = lean_box(0);
v_xs_x27_599_ = lean_array_fset(v_vs_590_, v___x_591_, v___x_598_);
v___x_600_ = lean_box(6);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_p_562_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_PersistentArray_push___redArg(v_v_597_, v___x_601_);
v___x_603_ = lean_array_fset(v_xs_x27_599_, v___x_591_, v___x_602_);
lean_dec(v___x_591_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_603_);
v___x_605_ = v___x_595_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0___boxed(lean_object* v_p_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_266__boxed_613_; size_t v_x_267__boxed_614_; lean_object* v_res_615_; 
v_x_266__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_x_267__boxed_614_ = lean_unbox_usize(v_x_612_);
lean_dec(v_x_612_);
v_res_615_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_609_, v_x_610_, v_x_266__boxed_613_, v_x_267__boxed_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(lean_object* v_p_616_, lean_object* v_t_617_, lean_object* v_i_618_){
_start:
{
lean_object* v_root_619_; lean_object* v_tail_620_; lean_object* v_size_621_; size_t v_shift_622_; lean_object* v_tailOff_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_649_; 
v_root_619_ = lean_ctor_get(v_t_617_, 0);
v_tail_620_ = lean_ctor_get(v_t_617_, 1);
v_size_621_ = lean_ctor_get(v_t_617_, 2);
v_shift_622_ = lean_ctor_get_usize(v_t_617_, 4);
v_tailOff_623_ = lean_ctor_get(v_t_617_, 3);
v_isSharedCheck_649_ = !lean_is_exclusive(v_t_617_);
if (v_isSharedCheck_649_ == 0)
{
v___x_625_ = v_t_617_;
v_isShared_626_ = v_isSharedCheck_649_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tailOff_623_);
lean_inc(v_size_621_);
lean_inc(v_tail_620_);
lean_inc(v_root_619_);
lean_dec(v_t_617_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_649_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v_tailOff_623_, v_i_618_);
if (v___x_627_ == 0)
{
size_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_usize_of_nat(v_i_618_);
v___x_629_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0_spec__0(v_p_616_, v_root_619_, v___x_628_, v_shift_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_tail_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_632_, 4, v_shift_622_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_nat_sub(v_i_618_, v_tailOff_623_);
v___x_634_ = lean_array_get_size(v_tail_620_);
v___x_635_ = lean_nat_dec_lt(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v___x_633_);
lean_dec(v_p_616_);
if (v_isShared_626_ == 0)
{
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_root_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_tail_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_638_, 4, v_shift_622_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v_v_639_; lean_object* v___x_640_; lean_object* v_xs_x27_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v_v_639_ = lean_array_fget(v_tail_620_, v___x_633_);
v___x_640_ = lean_box(0);
v_xs_x27_641_ = lean_array_fset(v_tail_620_, v___x_633_, v___x_640_);
v___x_642_ = lean_box(6);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v_p_616_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_PersistentArray_push___redArg(v_v_639_, v___x_643_);
v___x_645_ = lean_array_fset(v_xs_x27_641_, v___x_633_, v___x_644_);
lean_dec(v___x_633_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_645_);
v___x_647_ = v___x_625_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_root_619_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_648_, 4, v_shift_622_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0___boxed(lean_object* v_p_650_, lean_object* v_t_651_, lean_object* v_i_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_650_, v_t_651_, v_i_652_);
lean_dec(v_i_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(lean_object* v_a_654_, lean_object* v_p_655_, lean_object* v_one_656_, lean_object* v_s_657_){
_start:
{
lean_object* v_structs_658_; lean_object* v_typeIdOf_659_; lean_object* v_exprToStructId_660_; lean_object* v_exprToStructIdEntries_661_; lean_object* v_forbiddenNatModules_662_; lean_object* v_natStructs_663_; lean_object* v_natTypeIdOf_664_; lean_object* v_exprToNatStructId_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_structs_658_ = lean_ctor_get(v_s_657_, 0);
v_typeIdOf_659_ = lean_ctor_get(v_s_657_, 1);
v_exprToStructId_660_ = lean_ctor_get(v_s_657_, 2);
v_exprToStructIdEntries_661_ = lean_ctor_get(v_s_657_, 3);
v_forbiddenNatModules_662_ = lean_ctor_get(v_s_657_, 4);
v_natStructs_663_ = lean_ctor_get(v_s_657_, 5);
v_natTypeIdOf_664_ = lean_ctor_get(v_s_657_, 6);
v_exprToNatStructId_665_ = lean_ctor_get(v_s_657_, 7);
v___x_666_ = lean_array_get_size(v_structs_658_);
v___x_667_ = lean_nat_dec_lt(v_a_654_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec(v_p_655_);
return v_s_657_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_729_; 
lean_inc_ref(v_exprToNatStructId_665_);
lean_inc_ref(v_natTypeIdOf_664_);
lean_inc_ref(v_natStructs_663_);
lean_inc_ref(v_forbiddenNatModules_662_);
lean_inc_ref(v_exprToStructIdEntries_661_);
lean_inc_ref(v_exprToStructId_660_);
lean_inc_ref(v_typeIdOf_659_);
lean_inc_ref(v_structs_658_);
v_isSharedCheck_729_ = !lean_is_exclusive(v_s_657_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_730_ = lean_ctor_get(v_s_657_, 7);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_s_657_, 6);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_s_657_, 5);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_s_657_, 4);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_s_657_, 3);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_s_657_, 2);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_s_657_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_s_657_, 0);
lean_dec(v_unused_737_);
v___x_669_ = v_s_657_;
v_isShared_670_ = v_isSharedCheck_729_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_s_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_729_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_v_671_; lean_object* v_id_672_; lean_object* v_ringId_x3f_673_; lean_object* v_type_674_; lean_object* v_u_675_; lean_object* v_intModuleInst_676_; lean_object* v_leInst_x3f_677_; lean_object* v_ltInst_x3f_678_; lean_object* v_lawfulOrderLTInst_x3f_679_; lean_object* v_isPreorderInst_x3f_680_; lean_object* v_orderedAddInst_x3f_681_; lean_object* v_isLinearInst_x3f_682_; lean_object* v_noNatDivInst_x3f_683_; lean_object* v_ringInst_x3f_684_; lean_object* v_commRingInst_x3f_685_; lean_object* v_orderedRingInst_x3f_686_; lean_object* v_fieldInst_x3f_687_; lean_object* v_charInst_x3f_688_; lean_object* v_zero_689_; lean_object* v_ofNatZero_690_; lean_object* v_one_x3f_691_; lean_object* v_leFn_x3f_692_; lean_object* v_ltFn_x3f_693_; lean_object* v_addFn_694_; lean_object* v_zsmulFn_695_; lean_object* v_nsmulFn_696_; lean_object* v_zsmulFn_x3f_697_; lean_object* v_nsmulFn_x3f_698_; lean_object* v_homomulFn_x3f_699_; lean_object* v_subFn_700_; lean_object* v_negFn_701_; lean_object* v_vars_702_; lean_object* v_varMap_703_; lean_object* v_lowers_704_; lean_object* v_uppers_705_; lean_object* v_diseqs_706_; lean_object* v_assignment_707_; uint8_t v_caseSplits_708_; lean_object* v_conflict_x3f_709_; lean_object* v_diseqSplits_710_; lean_object* v_elimEqs_711_; lean_object* v_elimStack_712_; lean_object* v_occurs_713_; lean_object* v_ignored_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_728_; 
v_v_671_ = lean_array_fget(v_structs_658_, v_a_654_);
v_id_672_ = lean_ctor_get(v_v_671_, 0);
v_ringId_x3f_673_ = lean_ctor_get(v_v_671_, 1);
v_type_674_ = lean_ctor_get(v_v_671_, 2);
v_u_675_ = lean_ctor_get(v_v_671_, 3);
v_intModuleInst_676_ = lean_ctor_get(v_v_671_, 4);
v_leInst_x3f_677_ = lean_ctor_get(v_v_671_, 5);
v_ltInst_x3f_678_ = lean_ctor_get(v_v_671_, 6);
v_lawfulOrderLTInst_x3f_679_ = lean_ctor_get(v_v_671_, 7);
v_isPreorderInst_x3f_680_ = lean_ctor_get(v_v_671_, 8);
v_orderedAddInst_x3f_681_ = lean_ctor_get(v_v_671_, 9);
v_isLinearInst_x3f_682_ = lean_ctor_get(v_v_671_, 10);
v_noNatDivInst_x3f_683_ = lean_ctor_get(v_v_671_, 11);
v_ringInst_x3f_684_ = lean_ctor_get(v_v_671_, 12);
v_commRingInst_x3f_685_ = lean_ctor_get(v_v_671_, 13);
v_orderedRingInst_x3f_686_ = lean_ctor_get(v_v_671_, 14);
v_fieldInst_x3f_687_ = lean_ctor_get(v_v_671_, 15);
v_charInst_x3f_688_ = lean_ctor_get(v_v_671_, 16);
v_zero_689_ = lean_ctor_get(v_v_671_, 17);
v_ofNatZero_690_ = lean_ctor_get(v_v_671_, 18);
v_one_x3f_691_ = lean_ctor_get(v_v_671_, 19);
v_leFn_x3f_692_ = lean_ctor_get(v_v_671_, 20);
v_ltFn_x3f_693_ = lean_ctor_get(v_v_671_, 21);
v_addFn_694_ = lean_ctor_get(v_v_671_, 22);
v_zsmulFn_695_ = lean_ctor_get(v_v_671_, 23);
v_nsmulFn_696_ = lean_ctor_get(v_v_671_, 24);
v_zsmulFn_x3f_697_ = lean_ctor_get(v_v_671_, 25);
v_nsmulFn_x3f_698_ = lean_ctor_get(v_v_671_, 26);
v_homomulFn_x3f_699_ = lean_ctor_get(v_v_671_, 27);
v_subFn_700_ = lean_ctor_get(v_v_671_, 28);
v_negFn_701_ = lean_ctor_get(v_v_671_, 29);
v_vars_702_ = lean_ctor_get(v_v_671_, 30);
v_varMap_703_ = lean_ctor_get(v_v_671_, 31);
v_lowers_704_ = lean_ctor_get(v_v_671_, 32);
v_uppers_705_ = lean_ctor_get(v_v_671_, 33);
v_diseqs_706_ = lean_ctor_get(v_v_671_, 34);
v_assignment_707_ = lean_ctor_get(v_v_671_, 35);
v_caseSplits_708_ = lean_ctor_get_uint8(v_v_671_, sizeof(void*)*42);
v_conflict_x3f_709_ = lean_ctor_get(v_v_671_, 36);
v_diseqSplits_710_ = lean_ctor_get(v_v_671_, 37);
v_elimEqs_711_ = lean_ctor_get(v_v_671_, 38);
v_elimStack_712_ = lean_ctor_get(v_v_671_, 39);
v_occurs_713_ = lean_ctor_get(v_v_671_, 40);
v_ignored_714_ = lean_ctor_get(v_v_671_, 41);
v_isSharedCheck_728_ = !lean_is_exclusive(v_v_671_);
if (v_isSharedCheck_728_ == 0)
{
v___x_716_ = v_v_671_;
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_ignored_714_);
lean_inc(v_occurs_713_);
lean_inc(v_elimStack_712_);
lean_inc(v_elimEqs_711_);
lean_inc(v_diseqSplits_710_);
lean_inc(v_conflict_x3f_709_);
lean_inc(v_assignment_707_);
lean_inc(v_diseqs_706_);
lean_inc(v_uppers_705_);
lean_inc(v_lowers_704_);
lean_inc(v_varMap_703_);
lean_inc(v_vars_702_);
lean_inc(v_negFn_701_);
lean_inc(v_subFn_700_);
lean_inc(v_homomulFn_x3f_699_);
lean_inc(v_nsmulFn_x3f_698_);
lean_inc(v_zsmulFn_x3f_697_);
lean_inc(v_nsmulFn_696_);
lean_inc(v_zsmulFn_695_);
lean_inc(v_addFn_694_);
lean_inc(v_ltFn_x3f_693_);
lean_inc(v_leFn_x3f_692_);
lean_inc(v_one_x3f_691_);
lean_inc(v_ofNatZero_690_);
lean_inc(v_zero_689_);
lean_inc(v_charInst_x3f_688_);
lean_inc(v_fieldInst_x3f_687_);
lean_inc(v_orderedRingInst_x3f_686_);
lean_inc(v_commRingInst_x3f_685_);
lean_inc(v_ringInst_x3f_684_);
lean_inc(v_noNatDivInst_x3f_683_);
lean_inc(v_isLinearInst_x3f_682_);
lean_inc(v_orderedAddInst_x3f_681_);
lean_inc(v_isPreorderInst_x3f_680_);
lean_inc(v_lawfulOrderLTInst_x3f_679_);
lean_inc(v_ltInst_x3f_678_);
lean_inc(v_leInst_x3f_677_);
lean_inc(v_intModuleInst_676_);
lean_inc(v_u_675_);
lean_inc(v_type_674_);
lean_inc(v_ringId_x3f_673_);
lean_inc(v_id_672_);
lean_dec(v_v_671_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_728_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_xs_x27_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_718_ = lean_box(0);
v_xs_x27_719_ = lean_array_fset(v_structs_658_, v_a_654_, v___x_718_);
v___x_720_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne_spec__0(v_p_655_, v_diseqs_706_, v_one_656_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 34, v___x_720_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_id_672_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_ringId_x3f_673_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_type_674_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_u_675_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_intModuleInst_676_);
lean_ctor_set(v_reuseFailAlloc_727_, 5, v_leInst_x3f_677_);
lean_ctor_set(v_reuseFailAlloc_727_, 6, v_ltInst_x3f_678_);
lean_ctor_set(v_reuseFailAlloc_727_, 7, v_lawfulOrderLTInst_x3f_679_);
lean_ctor_set(v_reuseFailAlloc_727_, 8, v_isPreorderInst_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_727_, 9, v_orderedAddInst_x3f_681_);
lean_ctor_set(v_reuseFailAlloc_727_, 10, v_isLinearInst_x3f_682_);
lean_ctor_set(v_reuseFailAlloc_727_, 11, v_noNatDivInst_x3f_683_);
lean_ctor_set(v_reuseFailAlloc_727_, 12, v_ringInst_x3f_684_);
lean_ctor_set(v_reuseFailAlloc_727_, 13, v_commRingInst_x3f_685_);
lean_ctor_set(v_reuseFailAlloc_727_, 14, v_orderedRingInst_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_727_, 15, v_fieldInst_x3f_687_);
lean_ctor_set(v_reuseFailAlloc_727_, 16, v_charInst_x3f_688_);
lean_ctor_set(v_reuseFailAlloc_727_, 17, v_zero_689_);
lean_ctor_set(v_reuseFailAlloc_727_, 18, v_ofNatZero_690_);
lean_ctor_set(v_reuseFailAlloc_727_, 19, v_one_x3f_691_);
lean_ctor_set(v_reuseFailAlloc_727_, 20, v_leFn_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_727_, 21, v_ltFn_x3f_693_);
lean_ctor_set(v_reuseFailAlloc_727_, 22, v_addFn_694_);
lean_ctor_set(v_reuseFailAlloc_727_, 23, v_zsmulFn_695_);
lean_ctor_set(v_reuseFailAlloc_727_, 24, v_nsmulFn_696_);
lean_ctor_set(v_reuseFailAlloc_727_, 25, v_zsmulFn_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_727_, 26, v_nsmulFn_x3f_698_);
lean_ctor_set(v_reuseFailAlloc_727_, 27, v_homomulFn_x3f_699_);
lean_ctor_set(v_reuseFailAlloc_727_, 28, v_subFn_700_);
lean_ctor_set(v_reuseFailAlloc_727_, 29, v_negFn_701_);
lean_ctor_set(v_reuseFailAlloc_727_, 30, v_vars_702_);
lean_ctor_set(v_reuseFailAlloc_727_, 31, v_varMap_703_);
lean_ctor_set(v_reuseFailAlloc_727_, 32, v_lowers_704_);
lean_ctor_set(v_reuseFailAlloc_727_, 33, v_uppers_705_);
lean_ctor_set(v_reuseFailAlloc_727_, 34, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_727_, 35, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_727_, 36, v_conflict_x3f_709_);
lean_ctor_set(v_reuseFailAlloc_727_, 37, v_diseqSplits_710_);
lean_ctor_set(v_reuseFailAlloc_727_, 38, v_elimEqs_711_);
lean_ctor_set(v_reuseFailAlloc_727_, 39, v_elimStack_712_);
lean_ctor_set(v_reuseFailAlloc_727_, 40, v_occurs_713_);
lean_ctor_set(v_reuseFailAlloc_727_, 41, v_ignored_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*42, v_caseSplits_708_);
v___x_722_ = v_reuseFailAlloc_727_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_array_fset(v_xs_x27_719_, v_a_654_, v___x_722_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_723_);
v___x_725_ = v___x_669_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_typeIdOf_659_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_exprToStructId_660_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_exprToStructIdEntries_661_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_forbiddenNatModules_662_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v_natStructs_663_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_natTypeIdOf_664_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v_exprToNatStructId_665_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed(lean_object* v_a_738_, lean_object* v_p_739_, lean_object* v_one_740_, lean_object* v_s_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0(v_a_738_, v_p_739_, v_one_740_, v_s_741_);
lean_dec(v_one_740_);
lean_dec(v_a_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(lean_object* v_one_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_p_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg___closed__0);
v___x_748_ = lean_box(0);
lean_inc(v_one_743_);
v_p_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_p_749_, 0, v___x_747_);
lean_ctor_set(v_p_749_, 1, v_one_743_);
lean_ctor_set(v_p_749_, 2, v___x_748_);
lean_inc(v_a_744_);
v___f_750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_750_, 0, v_a_744_);
lean_closure_set(v___f_750_, 1, v_p_749_);
lean_closure_set(v___f_750_, 2, v_one_743_);
v___x_751_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_752_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_751_, v___f_750_, v_a_745_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg___boxed(lean_object* v_one_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(lean_object* v_one_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_one_758_, v_a_759_, v_a_760_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___boxed(lean_object* v_one_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne(v_one_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec(v_a_774_);
lean_dec(v_a_773_);
return v_res_785_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(lean_object* v_isCharInst_x3f_786_){
_start:
{
if (lean_obj_tag(v_isCharInst_x3f_786_) == 0)
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
else
{
lean_object* v_val_788_; lean_object* v_snd_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_val_788_ = lean_ctor_get(v_isCharInst_x3f_786_, 0);
v_snd_789_ = lean_ctor_get(v_val_788_, 1);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_dec_eq(v_snd_789_, v___x_790_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; 
v___x_792_ = 1;
return v___x_792_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst___boxed(lean_object* v_isCharInst_x3f_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v_isCharInst_x3f_794_);
lean_dec(v_isCharInst_x3f_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_797_) == 1)
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_836_; 
v_val_809_ = lean_ctor_get(v_ringId_x3f_797_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_ringId_x3f_797_);
if (v_isSharedCheck_836_ == 0)
{
v___x_811_ = v_ringId_x3f_797_;
v_isShared_812_ = v_isSharedCheck_836_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v_ringId_x3f_797_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_836_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = 0;
v___x_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_814_, 0, v_val_809_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_813_);
v___x_815_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_814_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec_ref_known(v___x_814_, 1);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_827_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_827_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_827_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_commRingInst_820_; lean_object* v___x_822_; 
v_commRingInst_820_ = lean_ctor_get(v_a_816_, 6);
lean_inc_ref(v_commRingInst_820_);
lean_dec(v_a_816_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_commRingInst_820_);
v___x_822_ = v___x_811_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_commRingInst_820_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_811_);
v_a_828_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_815_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_815_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_ringId_x3f_797_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec(v_a_840_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_866_, lean_object* v_type_867_, lean_object* v_commRingInst_x3f_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_868_) == 1)
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_888_; 
v_val_875_ = lean_ctor_get(v_commRingInst_x3f_868_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_commRingInst_x3f_868_);
if (v_isSharedCheck_888_ == 0)
{
v___x_877_ = v_commRingInst_x3f_868_;
v_isShared_878_ = v_isSharedCheck_888_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v_commRingInst_x3f_868_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_888_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v_u_866_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_mkConst(v___x_879_, v___x_881_);
v___x_883_ = l_Lean_mkAppB(v___x_882_, v_type_867_, v_val_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_883_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_887_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_commRingInst_x3f_868_);
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v_u_866_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_mkConst(v___x_889_, v___x_891_);
v___x_893_ = l_Lean_Expr_app___override(v___x_892_, v_type_867_);
v___x_894_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_893_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_895_, lean_object* v_type_896_, lean_object* v_commRingInst_x3f_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_895_, v_type_896_, v_commRingInst_x3f_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_905_, lean_object* v_type_906_, lean_object* v_commRingInst_x3f_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_905_, v_type_906_, v_commRingInst_x3f_907_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_920_, lean_object* v_type_921_, lean_object* v_commRingInst_x3f_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_920_, v_type_921_, v_commRingInst_x3f_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec(v_a_923_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_946_, lean_object* v_type_947_, lean_object* v_ringInst_x3f_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_948_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_968_; 
v_val_955_ = lean_ctor_get(v_ringInst_x3f_948_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v_ringInst_x3f_948_);
if (v_isSharedCheck_968_ == 0)
{
v___x_957_ = v_ringInst_x3f_948_;
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v_ringInst_x3f_948_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_961_, 0, v_u_946_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_mkConst(v___x_959_, v___x_961_);
v___x_963_ = l_Lean_mkAppB(v___x_962_, v_type_947_, v_val_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_963_);
v___x_965_ = v___x_957_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_ringInst_x3f_948_);
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_970_ = lean_box(0);
v___x_971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_971_, 0, v_u_946_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_mkConst(v___x_969_, v___x_971_);
v___x_973_ = l_Lean_Expr_app___override(v___x_972_, v_type_947_);
v___x_974_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_973_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_975_, lean_object* v_type_976_, lean_object* v_ringInst_x3f_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_975_, v_type_976_, v_ringInst_x3f_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_985_, lean_object* v_type_986_, lean_object* v_ringInst_x3f_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_985_, v_type_986_, v_ringInst_x3f_987_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1000_, lean_object* v_type_1001_, lean_object* v_ringInst_x3f_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1000_, v_type_1001_, v_ringInst_x3f_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec(v_a_1003_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1026_, lean_object* v_type_1027_, lean_object* v_ringInst_x3f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1028_) == 1)
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1048_; 
v_val_1035_ = lean_ctor_get(v_ringInst_x3f_1028_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_ringInst_x3f_1028_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1037_ = v_ringInst_x3f_1028_;
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v_ringInst_x3f_1028_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_u_1026_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_mkConst(v___x_1039_, v___x_1041_);
v___x_1043_ = l_Lean_mkAppB(v___x_1042_, v_type_1027_, v_val_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_ringInst_x3f_1028_);
v___x_1049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_u_1026_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_mkConst(v___x_1049_, v___x_1051_);
v___x_1053_ = l_Lean_Expr_app___override(v___x_1052_, v_type_1027_);
v___x_1054_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1053_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1055_, lean_object* v_type_1056_, lean_object* v_ringInst_x3f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1055_, v_type_1056_, v_ringInst_x3f_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1065_, lean_object* v_type_1066_, lean_object* v_ringInst_x3f_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1065_, v_type_1066_, v_ringInst_x3f_1067_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1080_, lean_object* v_type_1081_, lean_object* v_ringInst_x3f_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1080_, v_type_1081_, v_ringInst_x3f_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec(v_a_1083_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1102_, lean_object* v_type_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_u_1102_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_inc_ref(v___x_1117_);
v___x_1118_ = l_Lean_mkConst(v___x_1115_, v___x_1117_);
lean_inc_ref(v_type_1103_);
v___x_1119_ = l_Lean_Expr_app___override(v___x_1118_, v_type_1103_);
v___x_1120_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1119_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1202_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1202_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1202_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
if (lean_obj_tag(v_a_1121_) == 1)
{
lean_object* v_val_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1197_; 
lean_del_object(v___x_1123_);
v_val_1125_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1127_ = v_a_1121_;
v_isShared_1128_ = v_isSharedCheck_1197_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_val_1125_);
lean_dec(v_a_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1197_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1130_ = l_Lean_mkConst(v___x_1129_, v___x_1117_);
lean_inc_ref(v_type_1103_);
v___x_1131_ = l_Lean_mkAppB(v___x_1130_, v_type_1103_, v_val_1125_);
v___x_1132_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1131_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1188_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1188_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1188_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = l_Lean_Meta_mkNumeral(v_type_1103_, v___x_1144_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_n(v_a_1146_, 2);
lean_dec_ref_known(v___x_1145_, 1);
lean_inc(v_a_1133_);
v___x_1147_ = l_Lean_Meta_isDefEqD(v_a_1133_, v_a_1146_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; uint8_t v___x_1149_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = lean_unbox(v_a_1148_);
lean_dec(v_a_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1152_; 
lean_inc(v_a_1133_);
v___x_1150_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1133_, v_a_1146_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1108_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; uint8_t v_verbose_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v_verbose_1154_ = lean_ctor_get_uint8(v_a_1153_, 0);
lean_dec(v_a_1153_);
if (v_verbose_1154_ == 0)
{
lean_dec(v_a_1151_);
goto v___jp_1137_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_Sym_reportIssue(v_a_1151_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_dec_ref_known(v___x_1155_, 1);
goto v___jp_1137_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_del_object(v___x_1135_);
lean_dec(v_a_1133_);
lean_del_object(v___x_1127_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1151_);
lean_del_object(v___x_1135_);
lean_dec(v_a_1133_);
lean_del_object(v___x_1127_);
v_a_1164_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1152_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1152_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_dec(v_a_1146_);
goto v___jp_1137_;
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1146_);
lean_del_object(v___x_1135_);
lean_dec(v_a_1133_);
lean_del_object(v___x_1127_);
v_a_1172_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1147_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1147_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1135_);
lean_dec(v_a_1133_);
lean_del_object(v___x_1127_);
v_a_1180_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1145_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1145_);
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
v___jp_1137_:
{
lean_object* v___x_1139_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_a_1133_);
v___x_1139_ = v___x_1127_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1133_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1139_);
v___x_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_del_object(v___x_1127_);
lean_dec_ref(v_type_1103_);
v_a_1189_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1132_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1132_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_dec(v_a_1121_);
lean_dec_ref_known(v___x_1117_, 2);
lean_dec_ref(v_type_1103_);
v___x_1198_ = lean_box(0);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1198_);
v___x_1200_ = v___x_1123_;
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
else
{
lean_dec_ref_known(v___x_1117_, 2);
lean_dec_ref(v_type_1103_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1203_, lean_object* v_type_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1203_, v_type_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec(v_a_1205_);
return v_res_1216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1225_, lean_object* v_type_1226_, lean_object* v_semiringInst_x3f_1227_, lean_object* v_leInst_x3f_1228_, lean_object* v_ltInst_x3f_1229_, lean_object* v_preorderInst_x3f_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1227_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1228_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1229_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1230_) == 1)
{
lean_object* v_val_1241_; lean_object* v_val_1242_; lean_object* v_val_1243_; lean_object* v_val_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_isOrdType_1249_; lean_object* v___x_1250_; 
v_val_1241_ = lean_ctor_get(v_semiringInst_x3f_1227_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v_semiringInst_x3f_1227_, 1);
v_val_1242_ = lean_ctor_get(v_leInst_x3f_1228_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v_leInst_x3f_1228_, 1);
v_val_1243_ = lean_ctor_get(v_ltInst_x3f_1229_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v_ltInst_x3f_1229_, 1);
v_val_1244_ = lean_ctor_get(v_preorderInst_x3f_1230_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v_preorderInst_x3f_1230_, 1);
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_u_1225_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_mkConst(v___x_1245_, v___x_1247_);
v_isOrdType_1249_ = l_Lean_mkApp5(v___x_1248_, v_type_1226_, v_val_1241_, v_val_1242_, v_val_1243_, v_val_1244_);
lean_inc_ref(v_isOrdType_1249_);
v___x_1250_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1249_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
if (lean_obj_tag(v_a_1251_) == 1)
{
lean_dec_ref(v_isOrdType_1249_);
return v___x_1250_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1253_ = l_Lean_indentExpr(v_isOrdType_1249_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1231_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; uint8_t v_verbose_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_verbose_1257_ = lean_ctor_get_uint8(v_a_1256_, 0);
lean_dec(v_a_1256_);
if (v_verbose_1257_ == 0)
{
lean_dec_ref_known(v___x_1254_, 2);
goto v___jp_1238_;
}
else
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_Sym_reportIssue(v___x_1254_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_dec_ref_known(v___x_1258_, 1);
goto v___jp_1238_;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref_known(v___x_1254_, 2);
v_a_1267_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1255_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1255_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1249_);
return v___x_1250_;
}
}
else
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref_known(v_leInst_x3f_1228_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1227_, 1);
lean_dec(v_preorderInst_x3f_1230_);
lean_dec_ref(v_type_1226_);
lean_dec(v_u_1225_);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_ltInst_x3f_1229_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v_ltInst_x3f_1229_, 0);
lean_dec(v_unused_1283_);
v___x_1276_ = v_ltInst_x3f_1229_;
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v_ltInst_x3f_1229_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_box(0);
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref_known(v_semiringInst_x3f_1227_, 1);
lean_dec(v_preorderInst_x3f_1230_);
lean_dec(v_ltInst_x3f_1229_);
lean_dec_ref(v_type_1226_);
lean_dec(v_u_1225_);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_leInst_x3f_1228_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v_leInst_x3f_1228_, 0);
lean_dec(v_unused_1292_);
v___x_1285_ = v_leInst_x3f_1228_;
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
else
{
lean_dec(v_leInst_x3f_1228_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_box(0);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
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
else
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_preorderInst_x3f_1230_);
lean_dec(v_ltInst_x3f_1229_);
lean_dec(v_leInst_x3f_1228_);
lean_dec_ref(v_type_1226_);
lean_dec(v_u_1225_);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_semiringInst_x3f_1227_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_semiringInst_x3f_1227_, 0);
lean_dec(v_unused_1301_);
v___x_1294_ = v_semiringInst_x3f_1227_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_semiringInst_x3f_1227_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec(v_preorderInst_x3f_1230_);
lean_dec(v_ltInst_x3f_1229_);
lean_dec(v_leInst_x3f_1228_);
lean_dec(v_semiringInst_x3f_1227_);
lean_dec_ref(v_type_1226_);
lean_dec(v_u_1225_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
v___jp_1238_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1304_, lean_object* v_type_1305_, lean_object* v_semiringInst_x3f_1306_, lean_object* v_leInst_x3f_1307_, lean_object* v_ltInst_x3f_1308_, lean_object* v_preorderInst_x3f_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1304_, v_type_1305_, v_semiringInst_x3f_1306_, v_leInst_x3f_1307_, v_ltInst_x3f_1308_, v_preorderInst_x3f_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1318_, lean_object* v_type_1319_, lean_object* v_semiringInst_x3f_1320_, lean_object* v_leInst_x3f_1321_, lean_object* v_ltInst_x3f_1322_, lean_object* v_preorderInst_x3f_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1318_, v_type_1319_, v_semiringInst_x3f_1320_, v_leInst_x3f_1321_, v_ltInst_x3f_1322_, v_preorderInst_x3f_1323_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1336_ = _args[0];
lean_object* v_type_1337_ = _args[1];
lean_object* v_semiringInst_x3f_1338_ = _args[2];
lean_object* v_leInst_x3f_1339_ = _args[3];
lean_object* v_ltInst_x3f_1340_ = _args[4];
lean_object* v_preorderInst_x3f_1341_ = _args[5];
lean_object* v_a_1342_ = _args[6];
lean_object* v_a_1343_ = _args[7];
lean_object* v_a_1344_ = _args[8];
lean_object* v_a_1345_ = _args[9];
lean_object* v_a_1346_ = _args[10];
lean_object* v_a_1347_ = _args[11];
lean_object* v_a_1348_ = _args[12];
lean_object* v_a_1349_ = _args[13];
lean_object* v_a_1350_ = _args[14];
lean_object* v_a_1351_ = _args[15];
lean_object* v_a_1352_ = _args[16];
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1336_, v_type_1337_, v_semiringInst_x3f_1338_, v_leInst_x3f_1339_, v_ltInst_x3f_1340_, v_preorderInst_x3f_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
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
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1364_, lean_object* v_type_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_natModuleType_1376_; lean_object* v___x_1377_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_u_1364_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_inc_ref(v___x_1374_);
v___x_1375_ = l_Lean_mkConst(v___x_1372_, v___x_1374_);
lean_inc_ref(v_type_1365_);
v_natModuleType_1376_ = l_Lean_Expr_app___override(v___x_1375_, v_type_1365_);
v___x_1377_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1376_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1391_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_del_object(v___x_1380_);
v_val_1382_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v_a_1378_, 1);
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1384_ = l_Lean_mkConst(v___x_1383_, v___x_1374_);
v___x_1385_ = l_Lean_mkAppB(v___x_1384_, v_type_1365_, v_val_1382_);
v___x_1386_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1385_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_a_1378_);
lean_dec_ref_known(v___x_1374_, 2);
lean_dec_ref(v_type_1365_);
v___x_1387_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1387_);
v___x_1389_ = v___x_1380_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1374_, 2);
lean_dec_ref(v_type_1365_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1392_, lean_object* v_type_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1392_, v_type_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1401_, lean_object* v_type_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1401_, v_type_1402_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1415_, lean_object* v_type_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1415_, v_type_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec(v_a_1417_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1429_, lean_object* v_u_1430_, lean_object* v_type_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_u_1430_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_mkConst(v_declName_1429_, v___x_1439_);
v___x_1441_ = l_Lean_Expr_app___override(v___x_1440_, v_type_1431_);
v___x_1442_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1441_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1443_, lean_object* v_u_1444_, lean_object* v_type_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1443_, v_u_1444_, v_type_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1453_, lean_object* v_u_1454_, lean_object* v_type_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1453_, v_u_1454_, v_type_1455_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1468_, lean_object* v_u_1469_, lean_object* v_type_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1468_, v_u_1469_, v_type_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec(v_a_1471_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1483_, lean_object* v_u_1484_, lean_object* v_type_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_u_1484_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_mkConst(v_declName_1483_, v___x_1494_);
v___x_1496_ = l_Lean_Expr_app___override(v___x_1495_, v_type_1485_);
v___x_1497_ = l_Lean_Meta_Sym_synthInstance(v___x_1496_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1498_, lean_object* v_u_1499_, lean_object* v_type_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1498_, v_u_1499_, v_type_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1509_, lean_object* v_u_1510_, lean_object* v_type_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1509_, v_u_1510_, v_type_1511_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1524_, lean_object* v_u_1525_, lean_object* v_type_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1524_, v_u_1525_, v_type_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
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
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1539_, lean_object* v_u_1540_, lean_object* v_type_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1549_ = lean_box(0);
lean_inc_n(v_u_1540_, 2);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_u_1540_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_u_1540_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_u_1540_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_mkConst(v_declName_1539_, v___x_1552_);
lean_inc_ref_n(v_type_1541_, 2);
v___x_1554_ = l_Lean_mkApp3(v___x_1553_, v_type_1541_, v_type_1541_, v_type_1541_);
v___x_1555_ = l_Lean_Meta_Sym_synthInstance(v___x_1554_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1556_, lean_object* v_u_1557_, lean_object* v_type_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1556_, v_u_1557_, v_type_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1567_, lean_object* v_u_1568_, lean_object* v_type_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1567_, v_u_1568_, v_type_1569_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1582_, lean_object* v_u_1583_, lean_object* v_type_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1582_, v_u_1583_, v_type_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec(v_a_1585_);
return v_res_1596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = l_Lean_Level_ofNat(v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1602_, lean_object* v_type_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1613_ = lean_box(0);
lean_inc(v_u_1602_);
v___x_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_u_1602_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_u_1602_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1612_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_mkConst(v___x_1611_, v___x_1616_);
v___x_1618_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1603_);
v___x_1619_ = l_Lean_mkApp3(v___x_1617_, v___x_1618_, v_type_1603_, v_type_1603_);
v___x_1620_ = l_Lean_Meta_Sym_synthInstance(v___x_1619_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1621_, lean_object* v_type_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1621_, v_type_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1631_, lean_object* v_type_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1631_, v_type_1632_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1645_, lean_object* v_type_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1645_, v_type_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec(v_a_1647_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1659_, lean_object* v_type_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1670_ = lean_box(0);
lean_inc(v_u_1659_);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_u_1659_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_u_1659_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1669_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_mkConst(v___x_1668_, v___x_1673_);
v___x_1675_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1660_);
v___x_1676_ = l_Lean_mkApp3(v___x_1674_, v___x_1675_, v_type_1660_, v_type_1660_);
v___x_1677_ = l_Lean_Meta_Sym_synthInstance(v___x_1676_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1678_, lean_object* v_type_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1678_, v_type_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1688_, lean_object* v_type_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1688_, v_type_1689_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1702_, lean_object* v_type_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1702_, v_type_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1716_, lean_object* v_parentInst_x3f_1717_, lean_object* v_childInst_x3f_1718_, lean_object* v_toFieldName_1719_, lean_object* v_u_1720_, lean_object* v_type_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1716_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1717_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1718_) == 1)
{
lean_object* v_val_1732_; lean_object* v_val_1733_; lean_object* v_val_1734_; lean_object* v_____do__lift_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___x_1787_; 
v_val_1732_ = lean_ctor_get(v_leInst_x3f_1716_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v_leInst_x3f_1716_, 1);
v_val_1733_ = lean_ctor_get(v_parentInst_x3f_1717_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v_parentInst_x3f_1717_, 1);
v_val_1734_ = lean_ctor_get(v_childInst_x3f_1718_, 0);
v___x_1787_ = l_Lean_leCarrierIsSort(v_a_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
if (v___x_1789_ == 0)
{
v_____do__lift_1736_ = v_u_1720_;
v___y_1737_ = v_a_1722_;
v___y_1738_ = v_a_1723_;
v___y_1739_ = v_a_1724_;
v___y_1740_ = v_a_1725_;
v___y_1741_ = v_a_1726_;
v___y_1742_ = v_a_1727_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Level_succ___override(v_u_1720_);
v_____do__lift_1736_ = v___x_1790_;
v___y_1737_ = v_a_1722_;
v___y_1738_ = v_a_1723_;
v___y_1739_ = v_a_1724_;
v___y_1740_ = v_a_1725_;
v___y_1741_ = v_a_1726_;
v___y_1742_ = v_a_1727_;
goto v___jp_1735_;
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_val_1733_);
lean_dec(v_val_1732_);
lean_dec_ref_known(v_childInst_x3f_1718_, 1);
lean_dec_ref(v_type_1721_);
lean_dec(v_u_1720_);
lean_dec(v_toFieldName_1719_);
v_a_1791_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1787_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1787_);
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
v___jp_1735_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_____do__lift_1736_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_mkConst(v_toFieldName_1719_, v___x_1744_);
lean_inc(v_val_1734_);
v___x_1746_ = l_Lean_mkApp3(v___x_1745_, v_type_1721_, v_val_1732_, v_val_1734_);
lean_inc_ref(v___x_1746_);
lean_inc(v_val_1733_);
v___x_1747_ = l_Lean_Meta_isDefEqD(v_val_1733_, v___x_1746_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1778_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1778_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1778_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_unbox(v_a_1748_);
lean_dec(v_a_1748_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v_a_1754_; lean_object* v___x_1755_; 
lean_del_object(v___x_1750_);
lean_dec_ref_known(v_childInst_x3f_1718_, 1);
v___x_1753_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1733_, v___x_1746_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1737_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; uint8_t v_verbose_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_verbose_1757_ = lean_ctor_get_uint8(v_a_1756_, 0);
lean_dec(v_a_1756_);
if (v_verbose_1757_ == 0)
{
lean_dec(v_a_1754_);
goto v___jp_1729_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_Sym_reportIssue(v_a_1754_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref_known(v___x_1758_, 1);
goto v___jp_1729_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1754_);
v_a_1767_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1755_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1755_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec_ref(v___x_1746_);
lean_dec(v_val_1733_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v_childInst_x3f_1718_);
v___x_1776_ = v___x_1750_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_childInst_x3f_1718_);
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
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___x_1746_);
lean_dec(v_val_1733_);
lean_dec_ref_known(v_childInst_x3f_1718_, 1);
v_a_1779_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1747_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1747_);
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
}
else
{
lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref_known(v_leInst_x3f_1716_, 1);
lean_dec_ref(v_type_1721_);
lean_dec(v_u_1720_);
lean_dec(v_toFieldName_1719_);
lean_dec(v_childInst_x3f_1718_);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_parentInst_x3f_1717_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_parentInst_x3f_1717_, 0);
lean_dec(v_unused_1807_);
v___x_1800_ = v_parentInst_x3f_1717_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_dec(v_parentInst_x3f_1717_);
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
lean_dec_ref(v_type_1721_);
lean_dec(v_u_1720_);
lean_dec(v_toFieldName_1719_);
lean_dec(v_childInst_x3f_1718_);
lean_dec(v_parentInst_x3f_1717_);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_leInst_x3f_1716_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_leInst_x3f_1716_, 0);
lean_dec(v_unused_1816_);
v___x_1809_ = v_leInst_x3f_1716_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_leInst_x3f_1716_);
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
lean_dec_ref(v_type_1721_);
lean_dec(v_u_1720_);
lean_dec(v_toFieldName_1719_);
lean_dec(v_childInst_x3f_1718_);
lean_dec(v_parentInst_x3f_1717_);
lean_dec(v_leInst_x3f_1716_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
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
lean_dec_ref_known(v_extraType_x3f_1935_, 1);
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
v___x_2027_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2026_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
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
lean_dec_ref_known(v___x_2023_, 2);
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
lean_dec_ref_known(v___x_2023_, 2);
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
v___x_2121_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2120_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
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
lean_dec_ref_known(v___x_2117_, 2);
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
lean_dec_ref_known(v___x_2117_, 2);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v_ks_2201_; lean_object* v_vs_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2228_; 
v_ks_2201_ = lean_ctor_get(v_x_2197_, 0);
v_vs_2202_ = lean_ctor_get(v_x_2197_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2204_ = v_x_2197_;
v_isShared_2205_ = v_isSharedCheck_2228_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_vs_2202_);
lean_inc(v_ks_2201_);
lean_dec(v_x_2197_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2228_;
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
lean_object* v_k_x27_2213_; size_t v___x_2214_; size_t v___x_2215_; uint8_t v___x_2216_; 
v_k_x27_2213_ = lean_array_fget_borrowed(v_ks_2201_, v_x_2198_);
v___x_2214_ = lean_ptr_addr(v_x_2199_);
v___x_2215_ = lean_ptr_addr(v_k_x27_2213_);
v___x_2216_ = lean_usize_dec_eq(v___x_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2218_; 
if (v_isShared_2205_ == 0)
{
v___x_2218_ = v___x_2204_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_ks_2201_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_vs_2202_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_add(v_x_2198_, v___x_2219_);
lean_dec(v_x_2198_);
v_x_2197_ = v___x_2218_;
v_x_2198_ = v___x_2220_;
goto _start;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2223_ = lean_array_fset(v_ks_2201_, v_x_2198_, v_x_2199_);
v___x_2224_ = lean_array_fset(v_vs_2202_, v_x_2198_, v_x_2200_);
lean_dec(v_x_2198_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2224_);
lean_ctor_set(v___x_2204_, 0, v___x_2223_);
v___x_2226_ = v___x_2204_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2229_, lean_object* v_k_2230_, lean_object* v_v_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2229_, v___x_2232_, v_k_2230_, v_v_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2235_, size_t v_x_2236_, size_t v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2235_) == 0)
{
lean_object* v_es_2240_; size_t v___x_2241_; size_t v___x_2242_; lean_object* v_j_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_es_2240_ = lean_ctor_get(v_x_2235_, 0);
v___x_2241_ = ((size_t)31ULL);
v___x_2242_ = lean_usize_land(v_x_2236_, v___x_2241_);
v_j_2243_ = lean_usize_to_nat(v___x_2242_);
v___x_2244_ = lean_array_get_size(v_es_2240_);
v___x_2245_ = lean_nat_dec_lt(v_j_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_dec(v_j_2243_);
lean_dec(v_x_2239_);
lean_dec_ref(v_x_2238_);
return v_x_2235_;
}
else
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2286_; 
lean_inc_ref(v_es_2240_);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_x_2235_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_x_2235_, 0);
lean_dec(v_unused_2287_);
v___x_2247_ = v_x_2235_;
v_isShared_2248_ = v_isSharedCheck_2286_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v_x_2235_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2286_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_v_2249_; lean_object* v___x_2250_; lean_object* v_xs_x27_2251_; lean_object* v___y_2253_; 
v_v_2249_ = lean_array_fget(v_es_2240_, v_j_2243_);
v___x_2250_ = lean_box(0);
v_xs_x27_2251_ = lean_array_fset(v_es_2240_, v_j_2243_, v___x_2250_);
switch(lean_obj_tag(v_v_2249_))
{
case 0:
{
lean_object* v_key_2258_; lean_object* v_val_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2271_; 
v_key_2258_ = lean_ctor_get(v_v_2249_, 0);
v_val_2259_ = lean_ctor_get(v_v_2249_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_v_2249_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2261_ = v_v_2249_;
v_isShared_2262_ = v_isSharedCheck_2271_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_val_2259_);
lean_inc(v_key_2258_);
lean_dec(v_v_2249_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2271_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
size_t v___x_2263_; size_t v___x_2264_; uint8_t v___x_2265_; 
v___x_2263_ = lean_ptr_addr(v_x_2238_);
v___x_2264_ = lean_ptr_addr(v_key_2258_);
v___x_2265_ = lean_usize_dec_eq(v___x_2263_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_del_object(v___x_2261_);
v___x_2266_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2258_, v_val_2259_, v_x_2238_, v_x_2239_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
v___y_2253_ = v___x_2267_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2269_; 
lean_dec(v_val_2259_);
lean_dec(v_key_2258_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v_x_2239_);
lean_ctor_set(v___x_2261_, 0, v_x_2238_);
v___x_2269_ = v___x_2261_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_x_2238_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_x_2239_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
v___y_2253_ = v___x_2269_;
goto v___jp_2252_;
}
}
}
}
case 1:
{
lean_object* v_node_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2284_; 
v_node_2272_ = lean_ctor_get(v_v_2249_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_v_2249_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2274_ = v_v_2249_;
v_isShared_2275_ = v_isSharedCheck_2284_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_node_2272_);
lean_dec(v_v_2249_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2284_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2276_ = ((size_t)5ULL);
v___x_2277_ = lean_usize_shift_right(v_x_2236_, v___x_2276_);
v___x_2278_ = ((size_t)1ULL);
v___x_2279_ = lean_usize_add(v_x_2237_, v___x_2278_);
v___x_2280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2272_, v___x_2277_, v___x_2279_, v_x_2238_, v_x_2239_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2280_);
v___x_2282_ = v___x_2274_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
v___y_2253_ = v___x_2282_;
goto v___jp_2252_;
}
}
}
default: 
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_x_2238_);
lean_ctor_set(v___x_2285_, 1, v_x_2239_);
v___y_2253_ = v___x_2285_;
goto v___jp_2252_;
}
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_array_fset(v_xs_x27_2251_, v_j_2243_, v___y_2253_);
lean_dec(v_j_2243_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2254_);
v___x_2256_ = v___x_2247_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
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
else
{
lean_object* v_ks_2288_; lean_object* v_vs_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2307_; 
v_ks_2288_ = lean_ctor_get(v_x_2235_, 0);
v_vs_2289_ = lean_ctor_get(v_x_2235_, 1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_x_2235_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2291_ = v_x_2235_;
v_isShared_2292_ = v_isSharedCheck_2307_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_vs_2289_);
lean_inc(v_ks_2288_);
lean_dec(v_x_2235_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2307_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_ks_2288_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_vs_2289_);
v___x_2294_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v_newNode_2295_; size_t v___x_2296_; uint8_t v___x_2297_; 
v_newNode_2295_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2294_, v_x_2238_, v_x_2239_);
v___x_2296_ = ((size_t)7ULL);
v___x_2297_ = lean_usize_dec_le(v___x_2296_, v_x_2237_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2295_);
v___x_2299_ = lean_unsigned_to_nat(4u);
v___x_2300_ = lean_nat_dec_lt(v___x_2298_, v___x_2299_);
lean_dec(v___x_2298_);
if (v___x_2300_ == 0)
{
lean_object* v_ks_2301_; lean_object* v_vs_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_ks_2301_ = lean_ctor_get(v_newNode_2295_, 0);
lean_inc_ref(v_ks_2301_);
v_vs_2302_ = lean_ctor_get(v_newNode_2295_, 1);
lean_inc_ref(v_vs_2302_);
lean_dec_ref(v_newNode_2295_);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2305_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2237_, v_ks_2301_, v_vs_2302_, v___x_2303_, v___x_2304_);
lean_dec_ref(v_vs_2302_);
lean_dec_ref(v_ks_2301_);
return v___x_2305_;
}
else
{
return v_newNode_2295_;
}
}
else
{
return v_newNode_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2308_, lean_object* v_keys_2309_, lean_object* v_vals_2310_, lean_object* v_i_2311_, lean_object* v_entries_2312_){
_start:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = lean_array_get_size(v_keys_2309_);
v___x_2314_ = lean_nat_dec_lt(v_i_2311_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec(v_i_2311_);
return v_entries_2312_;
}
else
{
lean_object* v_k_2315_; lean_object* v_v_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; uint64_t v___x_2320_; size_t v_h_2321_; size_t v___x_2322_; lean_object* v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; size_t v_h_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_k_2315_ = lean_array_fget_borrowed(v_keys_2309_, v_i_2311_);
v_v_2316_ = lean_array_fget_borrowed(v_vals_2310_, v_i_2311_);
v___x_2317_ = lean_ptr_addr(v_k_2315_);
v___x_2318_ = ((size_t)3ULL);
v___x_2319_ = lean_usize_shift_right(v___x_2317_, v___x_2318_);
v___x_2320_ = lean_usize_to_uint64(v___x_2319_);
v_h_2321_ = lean_uint64_to_usize(v___x_2320_);
v___x_2322_ = ((size_t)5ULL);
v___x_2323_ = lean_unsigned_to_nat(1u);
v___x_2324_ = ((size_t)1ULL);
v___x_2325_ = lean_usize_sub(v_depth_2308_, v___x_2324_);
v___x_2326_ = lean_usize_mul(v___x_2322_, v___x_2325_);
v_h_2327_ = lean_usize_shift_right(v_h_2321_, v___x_2326_);
v___x_2328_ = lean_nat_add(v_i_2311_, v___x_2323_);
lean_dec(v_i_2311_);
lean_inc(v_v_2316_);
lean_inc(v_k_2315_);
v___x_2329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2312_, v_h_2327_, v_depth_2308_, v_k_2315_, v_v_2316_);
v_i_2311_ = v___x_2328_;
v_entries_2312_ = v___x_2329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2331_, lean_object* v_keys_2332_, lean_object* v_vals_2333_, lean_object* v_i_2334_, lean_object* v_entries_2335_){
_start:
{
size_t v_depth_boxed_2336_; lean_object* v_res_2337_; 
v_depth_boxed_2336_ = lean_unbox_usize(v_depth_2331_);
lean_dec(v_depth_2331_);
v_res_2337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2336_, v_keys_2332_, v_vals_2333_, v_i_2334_, v_entries_2335_);
lean_dec_ref(v_vals_2333_);
lean_dec_ref(v_keys_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
size_t v_x_726987__boxed_2343_; size_t v_x_726988__boxed_2344_; lean_object* v_res_2345_; 
v_x_726987__boxed_2343_ = lean_unbox_usize(v_x_2339_);
lean_dec(v_x_2339_);
v_x_726988__boxed_2344_ = lean_unbox_usize(v_x_2340_);
lean_dec(v_x_2340_);
v_res_2345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2338_, v_x_726987__boxed_2343_, v_x_726988__boxed_2344_, v_x_2341_, v_x_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
size_t v___x_2349_; size_t v___x_2350_; size_t v___x_2351_; uint64_t v___x_2352_; size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2349_ = lean_ptr_addr(v_x_2347_);
v___x_2350_ = ((size_t)3ULL);
v___x_2351_ = lean_usize_shift_right(v___x_2349_, v___x_2350_);
v___x_2352_ = lean_usize_to_uint64(v___x_2351_);
v___x_2353_ = lean_uint64_to_usize(v___x_2352_);
v___x_2354_ = ((size_t)1ULL);
v___x_2355_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2346_, v___x_2353_, v___x_2354_, v_x_2347_, v_x_2348_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2356_, lean_object* v_s_2357_){
_start:
{
lean_object* v_structs_2358_; lean_object* v_typeIdOf_2359_; lean_object* v_exprToStructId_2360_; lean_object* v_exprToStructIdEntries_2361_; lean_object* v_forbiddenNatModules_2362_; lean_object* v_natStructs_2363_; lean_object* v_natTypeIdOf_2364_; lean_object* v_exprToNatStructId_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2374_; 
v_structs_2358_ = lean_ctor_get(v_s_2357_, 0);
v_typeIdOf_2359_ = lean_ctor_get(v_s_2357_, 1);
v_exprToStructId_2360_ = lean_ctor_get(v_s_2357_, 2);
v_exprToStructIdEntries_2361_ = lean_ctor_get(v_s_2357_, 3);
v_forbiddenNatModules_2362_ = lean_ctor_get(v_s_2357_, 4);
v_natStructs_2363_ = lean_ctor_get(v_s_2357_, 5);
v_natTypeIdOf_2364_ = lean_ctor_get(v_s_2357_, 6);
v_exprToNatStructId_2365_ = lean_ctor_get(v_s_2357_, 7);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_s_2357_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2367_ = v_s_2357_;
v_isShared_2368_ = v_isSharedCheck_2374_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_exprToNatStructId_2365_);
lean_inc(v_natTypeIdOf_2364_);
lean_inc(v_natStructs_2363_);
lean_inc(v_forbiddenNatModules_2362_);
lean_inc(v_exprToStructIdEntries_2361_);
lean_inc(v_exprToStructId_2360_);
lean_inc(v_typeIdOf_2359_);
lean_inc(v_structs_2358_);
lean_dec(v_s_2357_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2374_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2362_, v_type_2356_, v___x_2369_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 4, v___x_2370_);
v___x_2372_ = v___x_2367_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_structs_2358_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_typeIdOf_2359_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_exprToStructId_2360_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_exprToStructIdEntries_2361_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2373_, 5, v_natStructs_2363_);
lean_ctor_set(v_reuseFailAlloc_2373_, 6, v_natTypeIdOf_2364_);
lean_ctor_set(v_reuseFailAlloc_2373_, 7, v_exprToNatStructId_2365_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v___x_2375_, lean_object* v_s_2376_){
_start:
{
lean_object* v_structs_2377_; lean_object* v_typeIdOf_2378_; lean_object* v_exprToStructId_2379_; lean_object* v_exprToStructIdEntries_2380_; lean_object* v_forbiddenNatModules_2381_; lean_object* v_natStructs_2382_; lean_object* v_natTypeIdOf_2383_; lean_object* v_exprToNatStructId_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2392_; 
v_structs_2377_ = lean_ctor_get(v_s_2376_, 0);
v_typeIdOf_2378_ = lean_ctor_get(v_s_2376_, 1);
v_exprToStructId_2379_ = lean_ctor_get(v_s_2376_, 2);
v_exprToStructIdEntries_2380_ = lean_ctor_get(v_s_2376_, 3);
v_forbiddenNatModules_2381_ = lean_ctor_get(v_s_2376_, 4);
v_natStructs_2382_ = lean_ctor_get(v_s_2376_, 5);
v_natTypeIdOf_2383_ = lean_ctor_get(v_s_2376_, 6);
v_exprToNatStructId_2384_ = lean_ctor_get(v_s_2376_, 7);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_s_2376_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2386_ = v_s_2376_;
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_exprToNatStructId_2384_);
lean_inc(v_natTypeIdOf_2383_);
lean_inc(v_natStructs_2382_);
lean_inc(v_forbiddenNatModules_2381_);
lean_inc(v_exprToStructIdEntries_2380_);
lean_inc(v_exprToStructId_2379_);
lean_inc(v_typeIdOf_2378_);
lean_inc(v_structs_2377_);
lean_dec(v_s_2376_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2388_ = lean_array_push(v_structs_2377_, v___x_2375_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2388_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_typeIdOf_2378_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_exprToStructId_2379_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_exprToStructIdEntries_2380_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v_forbiddenNatModules_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 5, v_natStructs_2382_);
lean_ctor_set(v_reuseFailAlloc_2391_, 6, v_natTypeIdOf_2383_);
lean_ctor_set(v_reuseFailAlloc_2391_, 7, v_exprToNatStructId_2384_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v_a_2393_, lean_object* v_00___2394_){
_start:
{
if (lean_obj_tag(v_a_2393_) == 0)
{
uint8_t v___x_2395_; 
v___x_2395_ = 0;
return v___x_2395_;
}
else
{
uint8_t v___x_2396_; 
v___x_2396_ = 1;
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1___boxed(lean_object* v_a_2397_, lean_object* v_00___2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2397_, v_00___2398_);
lean_dec(v_a_2397_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = lean_unsigned_to_nat(32u);
v___x_2402_ = lean_mk_empty_array_with_capacity(v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1(void){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = l_Lean_mkRawNatLit(v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = l_Lean_Int_mkType;
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = l_Lean_Nat_mkType;
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___y_2528_; lean_object* v___y_2532_; lean_object* v___y_2533_; uint8_t v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; uint8_t v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; uint8_t v___y_2600_; lean_object* v___y_2622_; uint8_t v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; 
lean_inc_ref_n(v_type_2515_, 2);
v___f_2639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2639_, 0, v_type_2515_);
v___x_2640_ = l_Lean_Meta_getDecLevel_x3f(v_type_2515_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_3894_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_3894_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_3894_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
if (lean_obj_tag(v_a_2641_) == 1)
{
lean_object* v_val_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_3889_; 
lean_del_object(v___x_2643_);
v_val_2645_ = lean_ctor_get(v_a_2641_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_a_2641_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_2647_ = v_a_2641_;
v_isShared_2648_ = v_isSharedCheck_3889_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_val_2645_);
lean_dec(v_a_2641_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_3889_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_type_2515_);
v___x_2649_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_type_2515_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_3888_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_3888_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_3888_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___y_2655_; lean_object* v___y_2656_; uint8_t v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v_homomulFn_x3f_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2728_; lean_object* v___y_2729_; uint8_t v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v_ltFn_x3f_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2814_; lean_object* v___y_2815_; uint8_t v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_____do__lift_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2873_; lean_object* v___y_2874_; uint8_t v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v_leFn_x3f_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v_____do__lift_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v_charInst_x3f_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; uint8_t v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v_____do__lift_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v_____do__lift_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v_____do__lift_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v_____do__lift_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v_____do__lift_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v_____do__lift_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_leCarrierIsSort(v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; uint8_t v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = lean_unbox(v_a_3877_);
lean_dec(v_a_3877_);
if (v___x_3878_ == 0)
{
lean_inc(v_val_2645_);
v_____do__lift_3841_ = v_val_2645_;
v___y_3842_ = v_a_2516_;
v___y_3843_ = v_a_2517_;
v___y_3844_ = v_a_2518_;
v___y_3845_ = v_a_2519_;
v___y_3846_ = v_a_2520_;
v___y_3847_ = v_a_2521_;
v___y_3848_ = v_a_2522_;
v___y_3849_ = v_a_2523_;
v___y_3850_ = v_a_2524_;
v___y_3851_ = v_a_2525_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3879_; 
lean_inc(v_val_2645_);
v___x_3879_ = l_Lean_Level_succ___override(v_val_2645_);
v_____do__lift_3841_ = v___x_3879_;
v___y_3842_ = v_a_2516_;
v___y_3843_ = v_a_2517_;
v___y_3844_ = v_a_2518_;
v___y_3845_ = v_a_2519_;
v___y_3846_ = v_a_2520_;
v___y_3847_ = v_a_2521_;
v___y_3848_ = v_a_2522_;
v___y_3849_ = v_a_2523_;
v___y_3850_ = v_a_2524_;
v___y_3851_ = v_a_2525_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3880_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3876_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3876_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
v___jp_2654_:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2683_, v___y_2691_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_structs_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v_structs_2695_ = lean_ctor_get(v_a_2694_, 0);
lean_inc_ref(v_structs_2695_);
lean_dec(v_a_2694_);
v___x_2696_ = lean_array_get_size(v_structs_2695_);
lean_dec_ref(v_structs_2695_);
v___x_2697_ = lean_unsigned_to_nat(32u);
v___x_2698_ = lean_mk_empty_array_with_capacity(v___x_2697_);
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0);
v___x_2700_ = ((size_t)5ULL);
lean_inc(v___y_2671_);
v___x_2701_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2698_);
lean_ctor_set(v___x_2701_, 2, v___y_2671_);
lean_ctor_set(v___x_2701_, 3, v___y_2671_);
lean_ctor_set_usize(v___x_2701_, 4, v___x_2700_);
v___x_2702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2);
v___x_2703_ = lean_box(0);
v___x_2704_ = lean_box(0);
lean_inc_ref_n(v___x_2701_, 7);
lean_inc(v___y_2665_);
lean_inc(v___y_2679_);
lean_inc(v___y_2668_);
lean_inc(v___y_2655_);
lean_inc(v___y_2676_);
lean_inc(v___y_2656_);
v___x_2705_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2705_, 0, v___x_2696_);
lean_ctor_set(v___x_2705_, 1, v_a_2650_);
lean_ctor_set(v___x_2705_, 2, v_type_2515_);
lean_ctor_set(v___x_2705_, 3, v_val_2645_);
lean_ctor_set(v___x_2705_, 4, v___y_2660_);
lean_ctor_set(v___x_2705_, 5, v___y_2659_);
lean_ctor_set(v___x_2705_, 6, v___y_2674_);
lean_ctor_set(v___x_2705_, 7, v___y_2656_);
lean_ctor_set(v___x_2705_, 8, v___y_2658_);
lean_ctor_set(v___x_2705_, 9, v___y_2681_);
lean_ctor_set(v___x_2705_, 10, v___y_2661_);
lean_ctor_set(v___x_2705_, 11, v___y_2670_);
lean_ctor_set(v___x_2705_, 12, v___y_2676_);
lean_ctor_set(v___x_2705_, 13, v___y_2669_);
lean_ctor_set(v___x_2705_, 14, v___y_2655_);
lean_ctor_set(v___x_2705_, 15, v___y_2668_);
lean_ctor_set(v___x_2705_, 16, v___y_2679_);
lean_ctor_set(v___x_2705_, 17, v___y_2666_);
lean_ctor_set(v___x_2705_, 18, v___y_2664_);
lean_ctor_set(v___x_2705_, 19, v___y_2665_);
lean_ctor_set(v___x_2705_, 20, v___y_2667_);
lean_ctor_set(v___x_2705_, 21, v___y_2663_);
lean_ctor_set(v___x_2705_, 22, v___y_2662_);
lean_ctor_set(v___x_2705_, 23, v___y_2673_);
lean_ctor_set(v___x_2705_, 24, v___y_2677_);
lean_ctor_set(v___x_2705_, 25, v___y_2678_);
lean_ctor_set(v___x_2705_, 26, v___y_2680_);
lean_ctor_set(v___x_2705_, 27, v_homomulFn_x3f_2682_);
lean_ctor_set(v___x_2705_, 28, v___y_2672_);
lean_ctor_set(v___x_2705_, 29, v___y_2675_);
lean_ctor_set(v___x_2705_, 30, v___x_2701_);
lean_ctor_set(v___x_2705_, 31, v___x_2702_);
lean_ctor_set(v___x_2705_, 32, v___x_2701_);
lean_ctor_set(v___x_2705_, 33, v___x_2701_);
lean_ctor_set(v___x_2705_, 34, v___x_2701_);
lean_ctor_set(v___x_2705_, 35, v___x_2701_);
lean_ctor_set(v___x_2705_, 36, v___x_2703_);
lean_ctor_set(v___x_2705_, 37, v___x_2702_);
lean_ctor_set(v___x_2705_, 38, v___x_2701_);
lean_ctor_set(v___x_2705_, 39, v___x_2704_);
lean_ctor_set(v___x_2705_, 40, v___x_2701_);
lean_ctor_set(v___x_2705_, 41, v___x_2701_);
lean_ctor_set_uint8(v___x_2705_, sizeof(void*)*42, v___y_2657_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_2706_, 0, v___x_2705_);
v___x_2707_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2708_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2707_, v___f_2706_, v___y_2683_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_dec_ref_known(v___x_2708_, 1);
if (lean_obj_tag(v___y_2665_) == 1)
{
if (lean_obj_tag(v___y_2676_) == 0)
{
lean_dec_ref_known(v___y_2665_, 1);
lean_dec(v___y_2679_);
lean_dec(v___y_2668_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
v___y_2528_ = v___x_2696_;
goto v___jp_2527_;
}
else
{
lean_object* v_val_2709_; uint8_t v___x_2710_; 
lean_dec_ref_known(v___y_2676_, 1);
v_val_2709_ = lean_ctor_get(v___y_2665_, 0);
lean_inc(v_val_2709_);
lean_dec_ref_known(v___y_2665_, 1);
v___x_2710_ = 1;
if (lean_obj_tag(v___y_2655_) == 0)
{
if (v___y_2657_ == 0)
{
lean_dec(v___y_2656_);
v___y_2568_ = v___y_2657_;
v___y_2569_ = v___y_2684_;
v___y_2570_ = v_val_2709_;
v___y_2571_ = v___y_2685_;
v___y_2572_ = v___y_2683_;
v___y_2573_ = v___y_2691_;
v___y_2574_ = v___y_2687_;
v___y_2575_ = v___x_2696_;
v___y_2576_ = v___y_2688_;
v___y_2577_ = v___y_2689_;
v___y_2578_ = v___y_2692_;
v___y_2579_ = v___y_2690_;
v___y_2580_ = v___y_2679_;
v___y_2581_ = v___y_2668_;
v___y_2582_ = v___y_2686_;
goto v___jp_2567_;
}
else
{
v___y_2622_ = v___y_2656_;
v___y_2623_ = v___y_2657_;
v___y_2624_ = v___y_2684_;
v___y_2625_ = v_val_2709_;
v___y_2626_ = v___y_2685_;
v___y_2627_ = v___y_2683_;
v___y_2628_ = v___y_2691_;
v___y_2629_ = v___y_2687_;
v___y_2630_ = v___x_2696_;
v___y_2631_ = v___y_2688_;
v___y_2632_ = v___y_2689_;
v___y_2633_ = v___y_2692_;
v___y_2634_ = v___y_2690_;
v___y_2635_ = v___y_2679_;
v___y_2636_ = v___x_2710_;
v___y_2637_ = v___y_2668_;
v___y_2638_ = v___y_2686_;
goto v___jp_2621_;
}
}
else
{
lean_dec_ref_known(v___y_2655_, 1);
v___y_2622_ = v___y_2656_;
v___y_2623_ = v___y_2657_;
v___y_2624_ = v___y_2684_;
v___y_2625_ = v_val_2709_;
v___y_2626_ = v___y_2685_;
v___y_2627_ = v___y_2683_;
v___y_2628_ = v___y_2691_;
v___y_2629_ = v___y_2687_;
v___y_2630_ = v___x_2696_;
v___y_2631_ = v___y_2688_;
v___y_2632_ = v___y_2689_;
v___y_2633_ = v___y_2692_;
v___y_2634_ = v___y_2690_;
v___y_2635_ = v___y_2679_;
v___y_2636_ = v___x_2710_;
v___y_2637_ = v___y_2668_;
v___y_2638_ = v___y_2686_;
goto v___jp_2621_;
}
}
}
else
{
lean_dec(v___y_2679_);
lean_dec(v___y_2676_);
lean_dec(v___y_2668_);
lean_dec(v___y_2665_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
v___y_2528_ = v___x_2696_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___y_2679_);
lean_dec(v___y_2676_);
lean_dec(v___y_2668_);
lean_dec(v___y_2665_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
v_a_2711_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2708_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2708_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_homomulFn_x3f_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec(v_a_2650_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2719_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2693_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2693_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
v___jp_2727_:
{
lean_object* v___x_2765_; 
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_2765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2645_, v_type_2515_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_2767_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2645_, v_type_2515_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2767_) == 0)
{
if (lean_obj_tag(v___y_2742_) == 0)
{
lean_object* v_a_2768_; 
lean_dec(v___y_2737_);
lean_del_object(v___x_2647_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2655_ = v___y_2729_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2730_;
v___y_2658_ = v___y_2733_;
v___y_2659_ = v___y_2732_;
v___y_2660_ = v___y_2731_;
v___y_2661_ = v___y_2734_;
v___y_2662_ = v___y_2735_;
v___y_2663_ = v_ltFn_x3f_2754_;
v___y_2664_ = v___y_2736_;
v___y_2665_ = v___y_2738_;
v___y_2666_ = v___y_2740_;
v___y_2667_ = v___y_2739_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2743_;
v___y_2671_ = v___y_2744_;
v___y_2672_ = v___y_2745_;
v___y_2673_ = v___y_2747_;
v___y_2674_ = v___y_2748_;
v___y_2675_ = v___y_2749_;
v___y_2676_ = v___y_2750_;
v___y_2677_ = v___y_2751_;
v___y_2678_ = v_a_2766_;
v___y_2679_ = v___y_2752_;
v___y_2680_ = v_a_2768_;
v___y_2681_ = v___y_2753_;
v_homomulFn_x3f_2682_ = v___y_2746_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v___y_2756_;
v___y_2685_ = v___y_2757_;
v___y_2686_ = v___y_2758_;
v___y_2687_ = v___y_2759_;
v___y_2688_ = v___y_2760_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
goto v___jp_2654_;
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v___y_2746_);
v_a_2769_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2770_, v_val_2645_, v_type_2515_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6));
v___x_2774_ = l_Lean_mkConst(v___x_2773_, v___y_2737_);
lean_inc_ref_n(v_type_2515_, 3);
v___x_2775_ = l_Lean_mkApp4(v___x_2774_, v_type_2515_, v_type_2515_, v_type_2515_, v_a_2772_);
v___x_2776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2775_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v_a_2777_);
v___x_2779_ = v___x_2647_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
v___y_2655_ = v___y_2729_;
v___y_2656_ = v___y_2728_;
v___y_2657_ = v___y_2730_;
v___y_2658_ = v___y_2733_;
v___y_2659_ = v___y_2732_;
v___y_2660_ = v___y_2731_;
v___y_2661_ = v___y_2734_;
v___y_2662_ = v___y_2735_;
v___y_2663_ = v_ltFn_x3f_2754_;
v___y_2664_ = v___y_2736_;
v___y_2665_ = v___y_2738_;
v___y_2666_ = v___y_2740_;
v___y_2667_ = v___y_2739_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2743_;
v___y_2671_ = v___y_2744_;
v___y_2672_ = v___y_2745_;
v___y_2673_ = v___y_2747_;
v___y_2674_ = v___y_2748_;
v___y_2675_ = v___y_2749_;
v___y_2676_ = v___y_2750_;
v___y_2677_ = v___y_2751_;
v___y_2678_ = v_a_2766_;
v___y_2679_ = v___y_2752_;
v___y_2680_ = v_a_2769_;
v___y_2681_ = v___y_2753_;
v_homomulFn_x3f_2682_ = v___x_2779_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v___y_2756_;
v___y_2685_ = v___y_2757_;
v___y_2686_ = v___y_2758_;
v___y_2687_ = v___y_2759_;
v___y_2688_ = v___y_2760_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2769_);
lean_dec_ref_known(v___y_2742_, 1);
lean_dec(v_a_2766_);
lean_dec(v_ltFn_x3f_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2781_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2776_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2776_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2769_);
lean_dec_ref_known(v___y_2742_, 1);
lean_dec(v_a_2766_);
lean_dec(v_ltFn_x3f_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2789_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2771_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2771_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_a_2766_);
lean_dec(v_ltFn_x3f_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2797_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2767_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2767_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_ltFn_x3f_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2805_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2765_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2765_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__7));
lean_inc_ref(v___y_2822_);
v___x_2855_ = l_Lean_Name_mkStr2(v___y_2822_, v___x_2854_);
lean_inc(v___y_2836_);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_____do__lift_2843_);
lean_ctor_set(v___x_2856_, 1, v___y_2836_);
v___x_2857_ = l_Lean_mkConst(v___x_2855_, v___x_2856_);
lean_inc_ref(v_type_2515_);
v___x_2858_ = l_Lean_mkAppB(v___x_2857_, v_type_2515_, v___y_2840_);
v___x_2859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2858_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 1);
lean_ctor_set(v___x_2652_, 0, v_a_2860_);
v___x_2862_ = v___x_2652_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v___y_2728_ = v___y_2815_;
v___y_2729_ = v___y_2814_;
v___y_2730_ = v___y_2816_;
v___y_2731_ = v___y_2819_;
v___y_2732_ = v___y_2818_;
v___y_2733_ = v___y_2817_;
v___y_2734_ = v___y_2820_;
v___y_2735_ = v___y_2821_;
v___y_2736_ = v___y_2823_;
v___y_2737_ = v___y_2824_;
v___y_2738_ = v___y_2825_;
v___y_2739_ = v___y_2826_;
v___y_2740_ = v___y_2827_;
v___y_2741_ = v___y_2828_;
v___y_2742_ = v___y_2829_;
v___y_2743_ = v___y_2830_;
v___y_2744_ = v___y_2831_;
v___y_2745_ = v___y_2832_;
v___y_2746_ = v___y_2833_;
v___y_2747_ = v___y_2834_;
v___y_2748_ = v___y_2835_;
v___y_2749_ = v___y_2837_;
v___y_2750_ = v___y_2838_;
v___y_2751_ = v___y_2839_;
v___y_2752_ = v___y_2841_;
v___y_2753_ = v___y_2842_;
v_ltFn_x3f_2754_ = v___x_2862_;
v___y_2755_ = v___y_2844_;
v___y_2756_ = v___y_2845_;
v___y_2757_ = v___y_2846_;
v___y_2758_ = v___y_2847_;
v___y_2759_ = v___y_2848_;
v___y_2760_ = v___y_2849_;
v___y_2761_ = v___y_2850_;
v___y_2762_ = v___y_2851_;
v___y_2763_ = v___y_2852_;
v___y_2764_ = v___y_2853_;
goto v___jp_2727_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2864_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2859_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2859_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2872_:
{
if (lean_obj_tag(v___y_2893_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2912_; 
v_val_2911_ = lean_ctor_get(v___y_2893_, 0);
lean_inc(v_val_2911_);
v___x_2912_ = l_Lean_leCarrierIsSort(v___y_2909_, v___y_2910_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; uint8_t v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = lean_unbox(v_a_2913_);
lean_dec(v_a_2913_);
if (v___x_2914_ == 0)
{
lean_inc(v_val_2645_);
v___y_2814_ = v___y_2873_;
v___y_2815_ = v___y_2874_;
v___y_2816_ = v___y_2875_;
v___y_2817_ = v___y_2876_;
v___y_2818_ = v___y_2877_;
v___y_2819_ = v___y_2878_;
v___y_2820_ = v___y_2879_;
v___y_2821_ = v___y_2880_;
v___y_2822_ = v___y_2881_;
v___y_2823_ = v___y_2882_;
v___y_2824_ = v___y_2884_;
v___y_2825_ = v___y_2883_;
v___y_2826_ = v_leFn_x3f_2900_;
v___y_2827_ = v___y_2885_;
v___y_2828_ = v___y_2886_;
v___y_2829_ = v___y_2887_;
v___y_2830_ = v___y_2888_;
v___y_2831_ = v___y_2889_;
v___y_2832_ = v___y_2890_;
v___y_2833_ = v___y_2891_;
v___y_2834_ = v___y_2892_;
v___y_2835_ = v___y_2893_;
v___y_2836_ = v___y_2894_;
v___y_2837_ = v___y_2895_;
v___y_2838_ = v___y_2896_;
v___y_2839_ = v___y_2897_;
v___y_2840_ = v_val_2911_;
v___y_2841_ = v___y_2898_;
v___y_2842_ = v___y_2899_;
v_____do__lift_2843_ = v_val_2645_;
v___y_2844_ = v___y_2901_;
v___y_2845_ = v___y_2902_;
v___y_2846_ = v___y_2903_;
v___y_2847_ = v___y_2904_;
v___y_2848_ = v___y_2905_;
v___y_2849_ = v___y_2906_;
v___y_2850_ = v___y_2907_;
v___y_2851_ = v___y_2908_;
v___y_2852_ = v___y_2909_;
v___y_2853_ = v___y_2910_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2915_; 
lean_inc(v_val_2645_);
v___x_2915_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_2814_ = v___y_2873_;
v___y_2815_ = v___y_2874_;
v___y_2816_ = v___y_2875_;
v___y_2817_ = v___y_2876_;
v___y_2818_ = v___y_2877_;
v___y_2819_ = v___y_2878_;
v___y_2820_ = v___y_2879_;
v___y_2821_ = v___y_2880_;
v___y_2822_ = v___y_2881_;
v___y_2823_ = v___y_2882_;
v___y_2824_ = v___y_2884_;
v___y_2825_ = v___y_2883_;
v___y_2826_ = v_leFn_x3f_2900_;
v___y_2827_ = v___y_2885_;
v___y_2828_ = v___y_2886_;
v___y_2829_ = v___y_2887_;
v___y_2830_ = v___y_2888_;
v___y_2831_ = v___y_2889_;
v___y_2832_ = v___y_2890_;
v___y_2833_ = v___y_2891_;
v___y_2834_ = v___y_2892_;
v___y_2835_ = v___y_2893_;
v___y_2836_ = v___y_2894_;
v___y_2837_ = v___y_2895_;
v___y_2838_ = v___y_2896_;
v___y_2839_ = v___y_2897_;
v___y_2840_ = v_val_2911_;
v___y_2841_ = v___y_2898_;
v___y_2842_ = v___y_2899_;
v_____do__lift_2843_ = v___x_2915_;
v___y_2844_ = v___y_2901_;
v___y_2845_ = v___y_2902_;
v___y_2846_ = v___y_2903_;
v___y_2847_ = v___y_2904_;
v___y_2848_ = v___y_2905_;
v___y_2849_ = v___y_2906_;
v___y_2850_ = v___y_2907_;
v___y_2851_ = v___y_2908_;
v___y_2852_ = v___y_2909_;
v___y_2853_ = v___y_2910_;
goto v___jp_2813_;
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref_known(v___y_2893_, 1);
lean_dec(v_val_2911_);
lean_dec(v_leFn_x3f_2900_);
lean_dec(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2916_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2912_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_del_object(v___x_2652_);
lean_inc(v___y_2891_);
v___y_2728_ = v___y_2874_;
v___y_2729_ = v___y_2873_;
v___y_2730_ = v___y_2875_;
v___y_2731_ = v___y_2878_;
v___y_2732_ = v___y_2877_;
v___y_2733_ = v___y_2876_;
v___y_2734_ = v___y_2879_;
v___y_2735_ = v___y_2880_;
v___y_2736_ = v___y_2882_;
v___y_2737_ = v___y_2884_;
v___y_2738_ = v___y_2883_;
v___y_2739_ = v_leFn_x3f_2900_;
v___y_2740_ = v___y_2885_;
v___y_2741_ = v___y_2886_;
v___y_2742_ = v___y_2887_;
v___y_2743_ = v___y_2888_;
v___y_2744_ = v___y_2889_;
v___y_2745_ = v___y_2890_;
v___y_2746_ = v___y_2891_;
v___y_2747_ = v___y_2892_;
v___y_2748_ = v___y_2893_;
v___y_2749_ = v___y_2895_;
v___y_2750_ = v___y_2896_;
v___y_2751_ = v___y_2897_;
v___y_2752_ = v___y_2898_;
v___y_2753_ = v___y_2899_;
v_ltFn_x3f_2754_ = v___y_2891_;
v___y_2755_ = v___y_2901_;
v___y_2756_ = v___y_2902_;
v___y_2757_ = v___y_2903_;
v___y_2758_ = v___y_2904_;
v___y_2759_ = v___y_2905_;
v___y_2760_ = v___y_2906_;
v___y_2761_ = v___y_2907_;
v___y_2762_ = v___y_2908_;
v___y_2763_ = v___y_2909_;
v___y_2764_ = v___y_2910_;
goto v___jp_2727_;
}
}
v___jp_2924_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v___y_2931_);
v___x_2966_ = l_Lean_Name_mkStr2(v___y_2931_, v___x_2965_);
lean_inc(v___y_2947_);
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_____do__lift_2954_);
lean_ctor_set(v___x_2967_, 1, v___y_2947_);
v___x_2968_ = l_Lean_mkConst(v___x_2966_, v___x_2967_);
lean_inc_ref(v_type_2515_);
v___x_2969_ = l_Lean_mkAppB(v___x_2968_, v_type_2515_, v___y_2949_);
v___x_2970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2969_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_a_2971_);
v___y_2873_ = v___y_2926_;
v___y_2874_ = v___y_2925_;
v___y_2875_ = v___y_2927_;
v___y_2876_ = v___y_2930_;
v___y_2877_ = v___y_2929_;
v___y_2878_ = v___y_2928_;
v___y_2879_ = v___y_2932_;
v___y_2880_ = v___y_2933_;
v___y_2881_ = v___y_2934_;
v___y_2882_ = v___y_2935_;
v___y_2883_ = v___y_2936_;
v___y_2884_ = v___y_2937_;
v___y_2885_ = v___y_2938_;
v___y_2886_ = v___y_2939_;
v___y_2887_ = v___y_2940_;
v___y_2888_ = v___y_2941_;
v___y_2889_ = v___y_2942_;
v___y_2890_ = v___y_2943_;
v___y_2891_ = v___y_2944_;
v___y_2892_ = v___y_2945_;
v___y_2893_ = v___y_2946_;
v___y_2894_ = v___y_2947_;
v___y_2895_ = v___y_2948_;
v___y_2896_ = v___y_2950_;
v___y_2897_ = v___y_2951_;
v___y_2898_ = v___y_2952_;
v___y_2899_ = v___y_2953_;
v_leFn_x3f_2900_ = v___x_2972_;
v___y_2901_ = v___y_2955_;
v___y_2902_ = v___y_2956_;
v___y_2903_ = v___y_2957_;
v___y_2904_ = v___y_2958_;
v___y_2905_ = v___y_2959_;
v___y_2906_ = v___y_2960_;
v___y_2907_ = v___y_2961_;
v___y_2908_ = v___y_2962_;
v___y_2909_ = v___y_2963_;
v___y_2910_ = v___y_2964_;
goto v___jp_2872_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2926_);
lean_dec(v___y_2925_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_2973_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2970_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2970_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
v___jp_2981_:
{
lean_object* v___x_3020_; 
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2645_, v_type_2515_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_3022_, v_val_2645_, v_type_2515_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_n(v_a_3024_, 2);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
lean_inc(v___y_3007_);
v___x_3026_ = l_Lean_mkConst(v___x_3025_, v___y_3007_);
lean_inc_ref(v_type_2515_);
v___x_3027_ = l_Lean_mkAppB(v___x_3026_, v_type_2515_, v_a_3024_);
v___x_3028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3027_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_3007_);
v___x_3031_ = l_Lean_mkConst(v___x_3030_, v___y_3007_);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15);
lean_inc_ref(v_type_2515_);
v___x_3034_ = l_Lean_mkAppB(v___x_3031_, v_type_2515_, v___x_3033_);
v___x_3035_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3034_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3249_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3249_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3249_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
if (lean_obj_tag(v_a_3036_) == 1)
{
lean_object* v_val_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_del_object(v___x_3038_);
v_val_3040_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v_a_3036_, 1);
v___x_3041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
lean_inc(v___y_3007_);
v___x_3042_ = l_Lean_mkConst(v___x_3041_, v___y_3007_);
lean_inc_ref(v_type_2515_);
v___x_3043_ = l_Lean_mkApp3(v___x_3042_, v_type_2515_, v___x_3033_, v_val_3040_);
v___x_3044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3043_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc_n(v_a_3045_, 2);
lean_dec_ref_known(v___x_3044_, 1);
lean_inc(v_a_3029_);
v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_3029_, v_a_3045_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref_known(v___x_3046_, 1);
v___x_3047_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3048_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3047_, v_val_2645_, v_type_2515_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc_n(v_a_3049_, 2);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2998_);
v___x_3051_ = l_Lean_mkConst(v___x_3050_, v___y_2998_);
lean_inc_ref_n(v_type_2515_, 3);
v___x_3052_ = l_Lean_mkApp4(v___x_3051_, v_type_2515_, v_type_2515_, v_type_2515_, v_a_3049_);
v___x_3053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3052_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_3055_, v_val_2645_, v_type_2515_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc_n(v_a_3057_, 2);
lean_dec_ref_known(v___x_3056_, 1);
v___x_3058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
v___x_3059_ = l_Lean_mkConst(v___x_3058_, v___y_3007_);
lean_inc_ref(v_type_2515_);
v___x_3060_ = l_Lean_mkAppB(v___x_3059_, v_type_2515_, v_a_3057_);
v___x_3061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3060_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3063_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___x_3061_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3063_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2645_, v_type_2515_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc_n(v_a_3064_, 2);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___y_2986_);
v___x_3068_ = l_Lean_mkConst(v___x_3065_, v___x_3067_);
v___x_3069_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2515_, 2);
lean_inc_ref(v___x_3068_);
v___x_3070_ = l_Lean_mkApp4(v___x_3068_, v___x_3069_, v_type_2515_, v_type_2515_, v_a_3064_);
v___x_3071_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3070_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3073_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2645_, v_type_2515_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc_n(v_a_3074_, 2);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2515_, 2);
v___x_3076_ = l_Lean_mkApp4(v___x_3068_, v___x_3075_, v_type_2515_, v_type_2515_, v_a_3074_);
v___x_3077_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3076_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_3080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3081_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___x_3079_, v___x_3080_);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc_ref(v___y_2992_);
v___x_3082_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_3024_, v___y_2992_, v___x_3081_, v_val_2645_, v_type_2515_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec_ref_known(v___x_3082_, 1);
v___x_3083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3084_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___x_3079_, v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_3086_ = lean_box(0);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3087_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_3000_, v___y_2992_, v___x_3084_, v___x_3085_, v_val_2645_, v_type_2515_, v___x_3086_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3087_, 1);
v___x_3088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3089_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___y_3003_, v___x_3088_);
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc_ref(v___y_2987_);
v___x_3091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3049_, v___y_2987_, v___x_3089_, v___x_3090_, v_val_2645_, v_type_2515_, v___x_3086_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref_known(v___x_3091_, 1);
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
lean_inc_ref(v___y_3003_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3093_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___y_3003_, v___x_3092_);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_3057_, v___y_2987_, v___x_3093_, v_val_2645_, v_type_2515_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref_known(v___x_3094_, 1);
v___x_3095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2985_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3096_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___y_2985_, v___x_3095_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_3098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc_ref(v___y_2988_);
v___x_3099_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3064_, v___y_2988_, v___x_3096_, v___x_3097_, v_val_2645_, v_type_2515_, v___x_3098_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref_known(v___x_3099_, 1);
v___x_3100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2985_);
lean_inc_ref(v___y_2997_);
lean_inc_ref(v___y_2994_);
v___x_3101_ = l_Lean_Name_mkStr4(v___y_2994_, v___y_2997_, v___y_2985_, v___x_3100_);
v___x_3102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__40);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc_ref(v___y_2988_);
v___x_3103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_3074_, v___y_2988_, v___x_3101_, v___x_3097_, v_val_2645_, v_type_2515_, v___x_3102_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_dec_ref_known(v___x_3103_, 1);
if (lean_obj_tag(v___y_2989_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3105_; 
v_val_3104_ = lean_ctor_get(v___y_2989_, 0);
lean_inc(v_val_3104_);
v___x_3105_ = l_Lean_leCarrierIsSort(v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; uint8_t v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
if (v___x_3107_ == 0)
{
lean_inc(v_val_2645_);
v___y_2925_ = v___y_2982_;
v___y_2926_ = v___y_2983_;
v___y_2927_ = v___y_2984_;
v___y_2928_ = v___y_2988_;
v___y_2929_ = v___y_2989_;
v___y_2930_ = v___y_2990_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2993_;
v___y_2933_ = v___y_2995_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v_a_3045_;
v___y_2936_ = v___y_2999_;
v___y_2937_ = v___y_2998_;
v___y_2938_ = v_a_3029_;
v___y_2939_ = v___y_3001_;
v___y_2940_ = v___y_3002_;
v___y_2941_ = v_a_3021_;
v___y_2942_ = v___x_3032_;
v___y_2943_ = v_a_3054_;
v___y_2944_ = v___x_3086_;
v___y_2945_ = v_a_3072_;
v___y_2946_ = v___y_3004_;
v___y_2947_ = v___y_3005_;
v___y_2948_ = v_a_3062_;
v___y_2949_ = v_val_3104_;
v___y_2950_ = v___y_3006_;
v___y_2951_ = v_a_3078_;
v___y_2952_ = v_charInst_x3f_3009_;
v___y_2953_ = v___y_3008_;
v_____do__lift_2954_ = v_val_2645_;
v___y_2955_ = v___y_3010_;
v___y_2956_ = v___y_3011_;
v___y_2957_ = v___y_3012_;
v___y_2958_ = v___y_3013_;
v___y_2959_ = v___y_3014_;
v___y_2960_ = v___y_3015_;
v___y_2961_ = v___y_3016_;
v___y_2962_ = v___y_3017_;
v___y_2963_ = v___y_3018_;
v___y_2964_ = v___y_3019_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_3108_; 
lean_inc(v_val_2645_);
v___x_3108_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_2925_ = v___y_2982_;
v___y_2926_ = v___y_2983_;
v___y_2927_ = v___y_2984_;
v___y_2928_ = v___y_2988_;
v___y_2929_ = v___y_2989_;
v___y_2930_ = v___y_2990_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2993_;
v___y_2933_ = v___y_2995_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v_a_3045_;
v___y_2936_ = v___y_2999_;
v___y_2937_ = v___y_2998_;
v___y_2938_ = v_a_3029_;
v___y_2939_ = v___y_3001_;
v___y_2940_ = v___y_3002_;
v___y_2941_ = v_a_3021_;
v___y_2942_ = v___x_3032_;
v___y_2943_ = v_a_3054_;
v___y_2944_ = v___x_3086_;
v___y_2945_ = v_a_3072_;
v___y_2946_ = v___y_3004_;
v___y_2947_ = v___y_3005_;
v___y_2948_ = v_a_3062_;
v___y_2949_ = v_val_3104_;
v___y_2950_ = v___y_3006_;
v___y_2951_ = v_a_3078_;
v___y_2952_ = v_charInst_x3f_3009_;
v___y_2953_ = v___y_3008_;
v_____do__lift_2954_ = v___x_3108_;
v___y_2955_ = v___y_3010_;
v___y_2956_ = v___y_3011_;
v___y_2957_ = v___y_3012_;
v___y_2958_ = v___y_3013_;
v___y_2959_ = v___y_3014_;
v___y_2960_ = v___y_3015_;
v___y_2961_ = v___y_3016_;
v___y_2962_ = v___y_3017_;
v___y_2963_ = v___y_3018_;
v___y_2964_ = v___y_3019_;
goto v___jp_2924_;
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v_val_3104_);
lean_dec_ref_known(v___y_2989_, 1);
lean_dec(v_a_3078_);
lean_dec(v_a_3072_);
lean_dec(v_a_3062_);
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3109_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3105_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3105_);
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
v___y_2873_ = v___y_2983_;
v___y_2874_ = v___y_2982_;
v___y_2875_ = v___y_2984_;
v___y_2876_ = v___y_2990_;
v___y_2877_ = v___y_2989_;
v___y_2878_ = v___y_2988_;
v___y_2879_ = v___y_2993_;
v___y_2880_ = v___y_2995_;
v___y_2881_ = v___y_2996_;
v___y_2882_ = v_a_3045_;
v___y_2883_ = v___y_2999_;
v___y_2884_ = v___y_2998_;
v___y_2885_ = v_a_3029_;
v___y_2886_ = v___y_3001_;
v___y_2887_ = v___y_3002_;
v___y_2888_ = v_a_3021_;
v___y_2889_ = v___x_3032_;
v___y_2890_ = v_a_3054_;
v___y_2891_ = v___x_3086_;
v___y_2892_ = v_a_3072_;
v___y_2893_ = v___y_3004_;
v___y_2894_ = v___y_3005_;
v___y_2895_ = v_a_3062_;
v___y_2896_ = v___y_3006_;
v___y_2897_ = v_a_3078_;
v___y_2898_ = v_charInst_x3f_3009_;
v___y_2899_ = v___y_3008_;
v_leFn_x3f_2900_ = v___x_3086_;
v___y_2901_ = v___y_3010_;
v___y_2902_ = v___y_3011_;
v___y_2903_ = v___y_3012_;
v___y_2904_ = v___y_3013_;
v___y_2905_ = v___y_3014_;
v___y_2906_ = v___y_3015_;
v___y_2907_ = v___y_3016_;
v___y_2908_ = v___y_3017_;
v___y_2909_ = v___y_3018_;
v___y_2910_ = v___y_3019_;
goto v___jp_2872_;
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v_a_3078_);
lean_dec(v_a_3072_);
lean_dec(v_a_3062_);
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3117_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3103_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3103_);
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
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3062_);
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3125_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3099_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3099_);
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
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3133_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3094_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3094_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3141_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3091_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3091_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3149_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3087_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3087_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_a_3078_);
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3157_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3082_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3082_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v_a_3074_);
lean_dec(v_a_3072_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3165_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3077_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3077_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_a_3072_);
lean_dec_ref(v___x_3068_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3173_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3073_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3073_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v___x_3068_);
lean_dec(v_a_3064_);
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3181_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3071_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3071_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3062_);
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3189_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3063_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3063_);
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
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3057_);
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3197_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3061_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3061_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v_a_3054_);
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3205_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3056_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3056_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_a_3049_);
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3213_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3053_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3053_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3221_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3048_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3048_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3229_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3046_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3046_);
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
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3237_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3044_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3044_);
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
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v_a_3036_);
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v___x_3245_ = lean_box(0);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3245_);
v___x_3247_ = v___x_3038_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_a_3029_);
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3250_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3035_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3035_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_a_3024_);
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3258_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3028_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3028_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v_a_3021_);
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3266_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3023_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3023_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v_charInst_x3f_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3004_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3274_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3020_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3020_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
v___jp_3282_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc(v___y_3288_);
lean_inc(v___y_3289_);
v___x_3313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v___y_3289_, v___y_3288_, v___y_3293_, v___x_3312_, v_val_2645_, v_type_2515_, v___y_3297_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__47));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
lean_inc(v___y_3289_);
v___x_3316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v___y_3289_, v_a_3314_, v___y_3291_, v___x_3315_, v_val_2645_, v_type_2515_, v___y_3297_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49));
lean_inc_n(v___y_3307_, 2);
v___x_3322_ = l_Lean_mkConst(v___x_3321_, v___y_3307_);
lean_inc_ref(v___y_3287_);
lean_inc_ref_n(v_type_2515_, 3);
v___x_3323_ = l_Lean_mkAppB(v___x_3322_, v_type_2515_, v___y_3287_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52));
v___x_3326_ = l_Lean_mkConst(v___x_3325_, v___y_3307_);
lean_inc_ref(v___x_3323_);
v___x_3327_ = l_Lean_mkAppB(v___x_3326_, v_type_2515_, v___x_3323_);
lean_inc(v___y_3305_);
lean_inc(v_val_2645_);
v___x_3328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2645_, v_type_2515_, v___y_3305_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__54));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3331_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3330_, v_val_2645_, v_type_2515_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3331_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2645_, v_type_2515_, v___y_3301_, v___y_3309_, v___y_3285_, v___y_3306_, v___y_3297_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
lean_inc(v___y_3288_);
lean_inc(v___y_3302_);
lean_inc(v___y_3289_);
lean_inc(v_a_3329_);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2645_, v_type_2515_, v_a_3329_, v___y_3289_, v___y_3302_, v___y_3288_, v___y_3297_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3335_) == 0)
{
if (lean_obj_tag(v_a_3329_) == 1)
{
lean_object* v_a_3336_; lean_object* v_val_3337_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v_val_3337_ = lean_ctor_get(v_a_3329_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v_a_3329_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3338_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_2645_, v_type_2515_, v_val_3337_, v___y_3297_, v___y_3295_, v___y_3300_, v___y_3308_, v___y_3284_, v___y_3304_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___y_2982_ = v___y_3283_;
v___y_2983_ = v_a_3336_;
v___y_2984_ = v___y_3311_;
v___y_2985_ = v___x_3320_;
v___y_2986_ = v___y_3286_;
v___y_2987_ = v___x_3323_;
v___y_2988_ = v___y_3287_;
v___y_2989_ = v___y_3289_;
v___y_2990_ = v___y_3288_;
v___y_2991_ = v___y_3290_;
v___y_2992_ = v___x_3327_;
v___y_2993_ = v_a_3317_;
v___y_2994_ = v___x_3318_;
v___y_2995_ = v___y_3292_;
v___y_2996_ = v___y_3294_;
v___y_2997_ = v___x_3319_;
v___y_2998_ = v___y_3296_;
v___y_2999_ = v_a_3334_;
v___y_3000_ = v___y_3298_;
v___y_3001_ = v_a_3332_;
v___y_3002_ = v___y_3299_;
v___y_3003_ = v___x_3324_;
v___y_3004_ = v___y_3302_;
v___y_3005_ = v___y_3303_;
v___y_3006_ = v___y_3305_;
v___y_3007_ = v___y_3307_;
v___y_3008_ = v___y_3310_;
v_charInst_x3f_3009_ = v_a_3339_;
v___y_3010_ = v___y_3301_;
v___y_3011_ = v___y_3309_;
v___y_3012_ = v___y_3285_;
v___y_3013_ = v___y_3306_;
v___y_3014_ = v___y_3297_;
v___y_3015_ = v___y_3295_;
v___y_3016_ = v___y_3300_;
v___y_3017_ = v___y_3308_;
v___y_3018_ = v___y_3284_;
v___y_3019_ = v___y_3304_;
goto v___jp_2981_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_a_3336_);
lean_dec(v_a_3334_);
lean_dec(v_a_3332_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3323_);
lean_dec(v_a_3317_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3340_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3338_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3338_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
lean_dec(v_a_3329_);
v_a_3348_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3349_ = lean_box(0);
v___y_2982_ = v___y_3283_;
v___y_2983_ = v_a_3348_;
v___y_2984_ = v___y_3311_;
v___y_2985_ = v___x_3320_;
v___y_2986_ = v___y_3286_;
v___y_2987_ = v___x_3323_;
v___y_2988_ = v___y_3287_;
v___y_2989_ = v___y_3289_;
v___y_2990_ = v___y_3288_;
v___y_2991_ = v___y_3290_;
v___y_2992_ = v___x_3327_;
v___y_2993_ = v_a_3317_;
v___y_2994_ = v___x_3318_;
v___y_2995_ = v___y_3292_;
v___y_2996_ = v___y_3294_;
v___y_2997_ = v___x_3319_;
v___y_2998_ = v___y_3296_;
v___y_2999_ = v_a_3334_;
v___y_3000_ = v___y_3298_;
v___y_3001_ = v_a_3332_;
v___y_3002_ = v___y_3299_;
v___y_3003_ = v___x_3324_;
v___y_3004_ = v___y_3302_;
v___y_3005_ = v___y_3303_;
v___y_3006_ = v___y_3305_;
v___y_3007_ = v___y_3307_;
v___y_3008_ = v___y_3310_;
v_charInst_x3f_3009_ = v___x_3349_;
v___y_3010_ = v___y_3301_;
v___y_3011_ = v___y_3309_;
v___y_3012_ = v___y_3285_;
v___y_3013_ = v___y_3306_;
v___y_3014_ = v___y_3297_;
v___y_3015_ = v___y_3295_;
v___y_3016_ = v___y_3300_;
v___y_3017_ = v___y_3308_;
v___y_3018_ = v___y_3284_;
v___y_3019_ = v___y_3304_;
goto v___jp_2981_;
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v_a_3334_);
lean_dec(v_a_3332_);
lean_dec(v_a_3329_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3323_);
lean_dec(v_a_3317_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3350_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3335_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3335_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_a_3332_);
lean_dec(v_a_3329_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3323_);
lean_dec(v_a_3317_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3358_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3333_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3333_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_a_3329_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3323_);
lean_dec(v_a_3317_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3366_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3331_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3331_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3323_);
lean_dec(v_a_3317_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3374_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3328_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3328_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3382_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3316_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3316_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3302_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec(v___y_3283_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v_a_3390_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3313_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3313_);
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
v___jp_3398_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3402_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; uint8_t v_ring_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v_ring_3430_ = lean_ctor_get_uint8(v_a_3429_, sizeof(void*)*18 + 22);
lean_dec(v_a_3429_);
if (v_ring_3430_ == 0)
{
lean_dec_ref(v___f_2639_);
v___y_3283_ = v___y_3399_;
v___y_3284_ = v___y_3400_;
v___y_3285_ = v___y_3402_;
v___y_3286_ = v___y_3401_;
v___y_3287_ = v___y_3404_;
v___y_3288_ = v___y_3427_;
v___y_3289_ = v___y_3403_;
v___y_3290_ = v___y_3405_;
v___y_3291_ = v___y_3406_;
v___y_3292_ = v___y_3407_;
v___y_3293_ = v___y_3409_;
v___y_3294_ = v___y_3408_;
v___y_3295_ = v___y_3410_;
v___y_3296_ = v___y_3411_;
v___y_3297_ = v___y_3412_;
v___y_3298_ = v___y_3413_;
v___y_3299_ = v___y_3415_;
v___y_3300_ = v___y_3416_;
v___y_3301_ = v___y_3417_;
v___y_3302_ = v___y_3418_;
v___y_3303_ = v___y_3419_;
v___y_3304_ = v___y_3420_;
v___y_3305_ = v___y_3421_;
v___y_3306_ = v___y_3422_;
v___y_3307_ = v___y_3423_;
v___y_3308_ = v___y_3424_;
v___y_3309_ = v___y_3425_;
v___y_3310_ = v___y_3426_;
v___y_3311_ = v_ring_3430_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = lean_box(0);
v___x_3432_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2650_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_dec_ref(v___f_2639_);
v___y_3283_ = v___y_3399_;
v___y_3284_ = v___y_3400_;
v___y_3285_ = v___y_3402_;
v___y_3286_ = v___y_3401_;
v___y_3287_ = v___y_3404_;
v___y_3288_ = v___y_3427_;
v___y_3289_ = v___y_3403_;
v___y_3290_ = v___y_3405_;
v___y_3291_ = v___y_3406_;
v___y_3292_ = v___y_3407_;
v___y_3293_ = v___y_3409_;
v___y_3294_ = v___y_3408_;
v___y_3295_ = v___y_3410_;
v___y_3296_ = v___y_3411_;
v___y_3297_ = v___y_3412_;
v___y_3298_ = v___y_3413_;
v___y_3299_ = v___y_3415_;
v___y_3300_ = v___y_3416_;
v___y_3301_ = v___y_3417_;
v___y_3302_ = v___y_3418_;
v___y_3303_ = v___y_3419_;
v___y_3304_ = v___y_3420_;
v___y_3305_ = v___y_3421_;
v___y_3306_ = v___y_3422_;
v___y_3307_ = v___y_3423_;
v___y_3308_ = v___y_3424_;
v___y_3309_ = v___y_3425_;
v___y_3310_ = v___y_3426_;
v___y_3311_ = v___x_3432_;
goto v___jp_3282_;
}
else
{
if (lean_obj_tag(v___y_3427_) == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v___y_3426_);
lean_dec(v___y_3423_);
lean_dec(v___y_3421_);
lean_dec(v___y_3418_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___y_3401_);
lean_dec(v___y_3399_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v___x_3433_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3433_, v___f_2639_, v___y_3417_);
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
lean_dec_ref(v___f_2639_);
v___y_3283_ = v___y_3399_;
v___y_3284_ = v___y_3400_;
v___y_3285_ = v___y_3402_;
v___y_3286_ = v___y_3401_;
v___y_3287_ = v___y_3404_;
v___y_3288_ = v___y_3427_;
v___y_3289_ = v___y_3403_;
v___y_3290_ = v___y_3405_;
v___y_3291_ = v___y_3406_;
v___y_3292_ = v___y_3407_;
v___y_3293_ = v___y_3409_;
v___y_3294_ = v___y_3408_;
v___y_3295_ = v___y_3410_;
v___y_3296_ = v___y_3411_;
v___y_3297_ = v___y_3412_;
v___y_3298_ = v___y_3413_;
v___y_3299_ = v___y_3415_;
v___y_3300_ = v___y_3416_;
v___y_3301_ = v___y_3417_;
v___y_3302_ = v___y_3418_;
v___y_3303_ = v___y_3419_;
v___y_3304_ = v___y_3420_;
v___y_3305_ = v___y_3421_;
v___y_3306_ = v___y_3422_;
v___y_3307_ = v___y_3423_;
v___y_3308_ = v___y_3424_;
v___y_3309_ = v___y_3425_;
v___y_3310_ = v___y_3426_;
v___y_3311_ = v___y_3414_;
goto v___jp_3282_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3423_);
lean_dec(v___y_3421_);
lean_dec(v___y_3418_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3411_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___y_3401_);
lean_dec(v___y_3399_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3452_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3428_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3428_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
v___jp_3460_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_box(0);
v___y_3399_ = v___y_3461_;
v___y_3400_ = v___y_3462_;
v___y_3401_ = v___y_3464_;
v___y_3402_ = v___y_3463_;
v___y_3403_ = v___y_3466_;
v___y_3404_ = v___y_3465_;
v___y_3405_ = v___y_3467_;
v___y_3406_ = v___y_3468_;
v___y_3407_ = v___y_3469_;
v___y_3408_ = v___y_3471_;
v___y_3409_ = v___y_3470_;
v___y_3410_ = v___y_3472_;
v___y_3411_ = v___y_3473_;
v___y_3412_ = v___y_3474_;
v___y_3413_ = v___y_3475_;
v___y_3414_ = v___y_3476_;
v___y_3415_ = v___y_3477_;
v___y_3416_ = v___y_3478_;
v___y_3417_ = v___y_3479_;
v___y_3418_ = v___y_3480_;
v___y_3419_ = v___y_3481_;
v___y_3420_ = v___y_3482_;
v___y_3421_ = v___y_3483_;
v___y_3422_ = v___y_3484_;
v___y_3423_ = v___y_3485_;
v___y_3424_ = v___y_3486_;
v___y_3425_ = v___y_3487_;
v___y_3426_ = v___y_3488_;
v___y_3427_ = v___x_3489_;
goto v___jp_3398_;
}
v___jp_3490_:
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_box(0);
v___y_3461_ = v___y_3491_;
v___y_3462_ = v___y_3516_;
v___y_3463_ = v___y_3510_;
v___y_3464_ = v___y_3492_;
v___y_3465_ = v___y_3494_;
v___y_3466_ = v___y_3493_;
v___y_3467_ = v___y_3496_;
v___y_3468_ = v___y_3499_;
v___y_3469_ = v___y_3500_;
v___y_3470_ = v___y_3502_;
v___y_3471_ = v___y_3501_;
v___y_3472_ = v___y_3513_;
v___y_3473_ = v___y_3504_;
v___y_3474_ = v___y_3512_;
v___y_3475_ = v___y_3505_;
v___y_3476_ = v___y_3507_;
v___y_3477_ = v___y_3506_;
v___y_3478_ = v___y_3514_;
v___y_3479_ = v___y_3508_;
v___y_3480_ = v___y_3495_;
v___y_3481_ = v___y_3497_;
v___y_3482_ = v___y_3517_;
v___y_3483_ = v___y_3498_;
v___y_3484_ = v___y_3511_;
v___y_3485_ = v___y_3503_;
v___y_3486_ = v___y_3515_;
v___y_3487_ = v___y_3509_;
v___y_3488_ = v___x_3518_;
goto v___jp_3460_;
}
v___jp_3519_:
{
lean_object* v___x_3539_; 
lean_inc(v_a_2650_);
v___x_3539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2650_, v___y_3535_, v___y_3536_, v___y_3527_, v___y_3521_, v___y_3534_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc_n(v_a_3540_, 2);
lean_dec_ref_known(v___x_3539_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2645_, v_type_2515_, v_a_3540_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc_n(v_a_3542_, 2);
lean_dec_ref_known(v___x_3541_, 1);
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3543_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2645_, v_type_2515_, v_a_3542_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3598_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3598_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3598_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
if (lean_obj_tag(v_a_3544_) == 1)
{
lean_object* v_val_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_del_object(v___x_3546_);
v_val_3548_ = lean_ctor_get(v_a_3544_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v_a_3544_, 1);
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_type_2515_);
lean_inc(v_val_2645_);
v___x_3550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3549_, v_val_2645_, v_type_2515_, v___y_3534_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc_n(v_a_3551_, 2);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3553_ = lean_box(0);
lean_inc_n(v_val_2645_, 3);
v___x_3554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_val_2645_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
lean_inc_ref(v___x_3554_);
v___x_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3555_, 0, v_val_2645_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
lean_inc_ref(v___x_3555_);
v___x_3556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3556_, 0, v_val_2645_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
lean_inc_ref(v___x_3556_);
v___x_3557_ = l_Lean_mkConst(v___x_3552_, v___x_3556_);
lean_inc_ref_n(v_type_2515_, 3);
v___x_3558_ = l_Lean_mkApp4(v___x_3557_, v_type_2515_, v_type_2515_, v_type_2515_, v_a_3551_);
v___x_3559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3558_, v___y_3534_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3559_) == 0)
{
if (lean_obj_tag(v___y_3524_) == 1)
{
if (lean_obj_tag(v___y_3532_) == 1)
{
lean_object* v_a_3560_; lean_object* v_val_3561_; lean_object* v_val_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v_val_3561_ = lean_ctor_get(v___y_3524_, 0);
v_val_3562_ = lean_ctor_get(v___y_3532_, 0);
v___x_3563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v___x_3554_);
v___x_3564_ = l_Lean_mkConst(v___x_3563_, v___x_3554_);
lean_inc(v_val_3562_);
lean_inc(v_val_3561_);
lean_inc(v_a_3551_);
lean_inc_ref(v_type_2515_);
v___x_3565_ = l_Lean_mkApp4(v___x_3564_, v_type_2515_, v_a_3551_, v_val_3561_, v_val_3562_);
v___x_3566_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3565_, v___y_3523_, v___y_3522_, v___y_3533_, v___y_3529_, v___y_3537_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
if (lean_obj_tag(v_a_3567_) == 0)
{
lean_dec_ref_known(v___y_3532_, 1);
v___y_3461_ = v___y_3520_;
v___y_3462_ = v___y_3529_;
v___y_3463_ = v___y_3527_;
v___y_3464_ = v___x_3555_;
v___y_3465_ = v_val_3548_;
v___y_3466_ = v___y_3524_;
v___y_3467_ = v___y_3525_;
v___y_3468_ = v___y_3528_;
v___y_3469_ = v_a_3560_;
v___y_3470_ = v___y_3530_;
v___y_3471_ = v___y_3531_;
v___y_3472_ = v___y_3523_;
v___y_3473_ = v___x_3556_;
v___y_3474_ = v___y_3534_;
v___y_3475_ = v_a_3551_;
v___y_3476_ = v___y_3538_;
v___y_3477_ = v_a_3540_;
v___y_3478_ = v___y_3522_;
v___y_3479_ = v___y_3535_;
v___y_3480_ = v___y_3526_;
v___y_3481_ = v___x_3553_;
v___y_3482_ = v___y_3537_;
v___y_3483_ = v_a_3542_;
v___y_3484_ = v___y_3521_;
v___y_3485_ = v___x_3554_;
v___y_3486_ = v___y_3533_;
v___y_3487_ = v___y_3536_;
v___y_3488_ = v_a_3567_;
goto v___jp_3460_;
}
else
{
if (v___y_3538_ == 0)
{
v___y_3399_ = v___y_3520_;
v___y_3400_ = v___y_3529_;
v___y_3401_ = v___x_3555_;
v___y_3402_ = v___y_3527_;
v___y_3403_ = v___y_3524_;
v___y_3404_ = v_val_3548_;
v___y_3405_ = v___y_3525_;
v___y_3406_ = v___y_3528_;
v___y_3407_ = v_a_3560_;
v___y_3408_ = v___y_3531_;
v___y_3409_ = v___y_3530_;
v___y_3410_ = v___y_3523_;
v___y_3411_ = v___x_3556_;
v___y_3412_ = v___y_3534_;
v___y_3413_ = v_a_3551_;
v___y_3414_ = v___y_3538_;
v___y_3415_ = v_a_3540_;
v___y_3416_ = v___y_3522_;
v___y_3417_ = v___y_3535_;
v___y_3418_ = v___y_3526_;
v___y_3419_ = v___x_3553_;
v___y_3420_ = v___y_3537_;
v___y_3421_ = v_a_3542_;
v___y_3422_ = v___y_3521_;
v___y_3423_ = v___x_3554_;
v___y_3424_ = v___y_3533_;
v___y_3425_ = v___y_3536_;
v___y_3426_ = v_a_3567_;
v___y_3427_ = v___y_3532_;
goto v___jp_3398_;
}
else
{
lean_dec_ref_known(v___y_3532_, 1);
v___y_3461_ = v___y_3520_;
v___y_3462_ = v___y_3529_;
v___y_3463_ = v___y_3527_;
v___y_3464_ = v___x_3555_;
v___y_3465_ = v_val_3548_;
v___y_3466_ = v___y_3524_;
v___y_3467_ = v___y_3525_;
v___y_3468_ = v___y_3528_;
v___y_3469_ = v_a_3560_;
v___y_3470_ = v___y_3530_;
v___y_3471_ = v___y_3531_;
v___y_3472_ = v___y_3523_;
v___y_3473_ = v___x_3556_;
v___y_3474_ = v___y_3534_;
v___y_3475_ = v_a_3551_;
v___y_3476_ = v___y_3538_;
v___y_3477_ = v_a_3540_;
v___y_3478_ = v___y_3522_;
v___y_3479_ = v___y_3535_;
v___y_3480_ = v___y_3526_;
v___y_3481_ = v___x_3553_;
v___y_3482_ = v___y_3537_;
v___y_3483_ = v_a_3542_;
v___y_3484_ = v___y_3521_;
v___y_3485_ = v___x_3554_;
v___y_3486_ = v___y_3533_;
v___y_3487_ = v___y_3536_;
v___y_3488_ = v_a_3567_;
goto v___jp_3460_;
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec_ref_known(v___y_3532_, 1);
lean_dec(v_a_3560_);
lean_dec_ref_known(v___y_3524_, 1);
lean_dec_ref_known(v___x_3556_, 2);
lean_dec_ref_known(v___x_3555_, 2);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3551_);
lean_dec(v_val_3548_);
lean_dec(v_a_3542_);
lean_dec(v_a_3540_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3568_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3566_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3566_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; 
lean_dec(v___y_3532_);
v_a_3576_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3576_);
lean_dec_ref_known(v___x_3559_, 1);
v___y_3491_ = v___y_3520_;
v___y_3492_ = v___x_3555_;
v___y_3493_ = v___y_3524_;
v___y_3494_ = v_val_3548_;
v___y_3495_ = v___y_3526_;
v___y_3496_ = v___y_3525_;
v___y_3497_ = v___x_3553_;
v___y_3498_ = v_a_3542_;
v___y_3499_ = v___y_3528_;
v___y_3500_ = v_a_3576_;
v___y_3501_ = v___y_3531_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___x_3554_;
v___y_3504_ = v___x_3556_;
v___y_3505_ = v_a_3551_;
v___y_3506_ = v_a_3540_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3535_;
v___y_3509_ = v___y_3536_;
v___y_3510_ = v___y_3527_;
v___y_3511_ = v___y_3521_;
v___y_3512_ = v___y_3534_;
v___y_3513_ = v___y_3523_;
v___y_3514_ = v___y_3522_;
v___y_3515_ = v___y_3533_;
v___y_3516_ = v___y_3529_;
v___y_3517_ = v___y_3537_;
goto v___jp_3490_;
}
}
else
{
lean_object* v_a_3577_; 
lean_dec(v___y_3532_);
v_a_3577_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3559_, 1);
v___y_3491_ = v___y_3520_;
v___y_3492_ = v___x_3555_;
v___y_3493_ = v___y_3524_;
v___y_3494_ = v_val_3548_;
v___y_3495_ = v___y_3526_;
v___y_3496_ = v___y_3525_;
v___y_3497_ = v___x_3553_;
v___y_3498_ = v_a_3542_;
v___y_3499_ = v___y_3528_;
v___y_3500_ = v_a_3577_;
v___y_3501_ = v___y_3531_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___x_3554_;
v___y_3504_ = v___x_3556_;
v___y_3505_ = v_a_3551_;
v___y_3506_ = v_a_3540_;
v___y_3507_ = v___y_3538_;
v___y_3508_ = v___y_3535_;
v___y_3509_ = v___y_3536_;
v___y_3510_ = v___y_3527_;
v___y_3511_ = v___y_3521_;
v___y_3512_ = v___y_3534_;
v___y_3513_ = v___y_3523_;
v___y_3514_ = v___y_3522_;
v___y_3515_ = v___y_3533_;
v___y_3516_ = v___y_3529_;
v___y_3517_ = v___y_3537_;
goto v___jp_3490_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref_known(v___x_3556_, 2);
lean_dec_ref_known(v___x_3555_, 2);
lean_dec_ref_known(v___x_3554_, 2);
lean_dec(v_a_3551_);
lean_dec(v_val_3548_);
lean_dec(v_a_3542_);
lean_dec(v_a_3540_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3578_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3559_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3559_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_val_3548_);
lean_dec(v_a_3542_);
lean_dec(v_a_3540_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3586_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3550_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3550_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
lean_dec(v_a_3544_);
lean_dec(v_a_3542_);
lean_dec(v_a_3540_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v___x_3594_ = lean_box(0);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3594_);
v___x_3596_ = v___x_3546_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v_a_3542_);
lean_dec(v_a_3540_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3599_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3543_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3543_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v_a_3540_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3607_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3541_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3541_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
lean_dec(v___y_3528_);
lean_dec(v___y_3526_);
lean_dec(v___y_3524_);
lean_dec(v___y_3520_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3615_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3539_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3539_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
v___jp_3623_:
{
lean_object* v___x_3642_; 
lean_inc(v___y_3628_);
lean_inc_ref(v_type_2515_);
v___x_3642_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_____do__lift_3631_, v_type_2515_, v___y_3628_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3644_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3644_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3634_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; uint8_t v_ring_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v_ring_3646_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*18 + 22);
lean_dec(v_a_3645_);
if (v_ring_3646_ == 0)
{
v___y_3520_ = v___y_3624_;
v___y_3521_ = v___y_3635_;
v___y_3522_ = v___y_3638_;
v___y_3523_ = v___y_3637_;
v___y_3524_ = v___y_3628_;
v___y_3525_ = v___y_3630_;
v___y_3526_ = v___y_3629_;
v___y_3527_ = v___y_3634_;
v___y_3528_ = v_a_3643_;
v___y_3529_ = v___y_3640_;
v___y_3530_ = v___y_3626_;
v___y_3531_ = v___y_3625_;
v___y_3532_ = v___y_3627_;
v___y_3533_ = v___y_3639_;
v___y_3534_ = v___y_3636_;
v___y_3535_ = v___y_3632_;
v___y_3536_ = v___y_3633_;
v___y_3537_ = v___y_3641_;
v___y_3538_ = v_ring_3646_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_box(0);
v___x_3648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(v_a_2650_, v___x_3647_);
if (v___x_3648_ == 0)
{
v___y_3520_ = v___y_3624_;
v___y_3521_ = v___y_3635_;
v___y_3522_ = v___y_3638_;
v___y_3523_ = v___y_3637_;
v___y_3524_ = v___y_3628_;
v___y_3525_ = v___y_3630_;
v___y_3526_ = v___y_3629_;
v___y_3527_ = v___y_3634_;
v___y_3528_ = v_a_3643_;
v___y_3529_ = v___y_3640_;
v___y_3530_ = v___y_3626_;
v___y_3531_ = v___y_3625_;
v___y_3532_ = v___y_3627_;
v___y_3533_ = v___y_3639_;
v___y_3534_ = v___y_3636_;
v___y_3535_ = v___y_3632_;
v___y_3536_ = v___y_3633_;
v___y_3537_ = v___y_3641_;
v___y_3538_ = v___x_3648_;
goto v___jp_3519_;
}
else
{
if (lean_obj_tag(v___y_3627_) == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec(v_a_3643_);
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
lean_dec(v___y_3624_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v_type_2515_);
v___x_3649_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3650_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3649_, v___f_2639_, v___y_3632_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v___x_3650_, 0);
lean_dec(v_unused_3659_);
v___x_3652_ = v___x_3650_;
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
else
{
lean_dec(v___x_3650_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = lean_box(0);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3650_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3650_);
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
uint8_t v___x_3668_; 
v___x_3668_ = 0;
v___y_3520_ = v___y_3624_;
v___y_3521_ = v___y_3635_;
v___y_3522_ = v___y_3638_;
v___y_3523_ = v___y_3637_;
v___y_3524_ = v___y_3628_;
v___y_3525_ = v___y_3630_;
v___y_3526_ = v___y_3629_;
v___y_3527_ = v___y_3634_;
v___y_3528_ = v_a_3643_;
v___y_3529_ = v___y_3640_;
v___y_3530_ = v___y_3626_;
v___y_3531_ = v___y_3625_;
v___y_3532_ = v___y_3627_;
v___y_3533_ = v___y_3639_;
v___y_3534_ = v___y_3636_;
v___y_3535_ = v___y_3632_;
v___y_3536_ = v___y_3633_;
v___y_3537_ = v___y_3641_;
v___y_3538_ = v___x_3668_;
goto v___jp_3519_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v_a_3643_);
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec(v___y_3624_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3669_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3644_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3644_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec(v___y_3624_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3677_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3642_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3642_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
v___jp_3685_:
{
lean_object* v___x_3703_; 
lean_inc(v___y_3689_);
lean_inc_ref(v_type_2515_);
v___x_3703_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_____do__lift_3692_, v_type_2515_, v___y_3689_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
v___x_3705_ = l_Lean_leCarrierIsSort(v___y_3701_, v___y_3702_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; uint8_t v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v___x_3707_ = lean_unbox(v_a_3706_);
lean_dec(v_a_3706_);
if (v___x_3707_ == 0)
{
lean_inc(v_val_2645_);
v___y_3624_ = v___y_3686_;
v___y_3625_ = v___y_3687_;
v___y_3626_ = v_a_3704_;
v___y_3627_ = v___y_3688_;
v___y_3628_ = v___y_3689_;
v___y_3629_ = v___y_3691_;
v___y_3630_ = v___y_3690_;
v_____do__lift_3631_ = v_val_2645_;
v___y_3632_ = v___y_3693_;
v___y_3633_ = v___y_3694_;
v___y_3634_ = v___y_3695_;
v___y_3635_ = v___y_3696_;
v___y_3636_ = v___y_3697_;
v___y_3637_ = v___y_3698_;
v___y_3638_ = v___y_3699_;
v___y_3639_ = v___y_3700_;
v___y_3640_ = v___y_3701_;
v___y_3641_ = v___y_3702_;
goto v___jp_3623_;
}
else
{
lean_object* v___x_3708_; 
lean_inc(v_val_2645_);
v___x_3708_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_3624_ = v___y_3686_;
v___y_3625_ = v___y_3687_;
v___y_3626_ = v_a_3704_;
v___y_3627_ = v___y_3688_;
v___y_3628_ = v___y_3689_;
v___y_3629_ = v___y_3691_;
v___y_3630_ = v___y_3690_;
v_____do__lift_3631_ = v___x_3708_;
v___y_3632_ = v___y_3693_;
v___y_3633_ = v___y_3694_;
v___y_3634_ = v___y_3695_;
v___y_3635_ = v___y_3696_;
v___y_3636_ = v___y_3697_;
v___y_3637_ = v___y_3698_;
v___y_3638_ = v___y_3699_;
v___y_3639_ = v___y_3700_;
v___y_3640_ = v___y_3701_;
v___y_3641_ = v___y_3702_;
goto v___jp_3623_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v_a_3704_);
lean_dec(v___y_3691_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec(v___y_3686_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3709_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3705_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3705_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v___y_3691_);
lean_dec(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec(v___y_3686_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3717_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3703_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3703_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
v___jp_3725_:
{
lean_object* v___x_3742_; 
lean_inc(v___y_3728_);
lean_inc_ref(v_type_2515_);
v___x_3742_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_____do__lift_3731_, v_type_2515_, v___y_3728_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_Lean_leCarrierIsSort(v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; uint8_t v___x_3746_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
v___x_3746_ = lean_unbox(v_a_3745_);
lean_dec(v_a_3745_);
if (v___x_3746_ == 0)
{
lean_inc(v_val_2645_);
v___y_3686_ = v___y_3726_;
v___y_3687_ = v___y_3727_;
v___y_3688_ = v_a_3743_;
v___y_3689_ = v___y_3728_;
v___y_3690_ = v___y_3730_;
v___y_3691_ = v___y_3729_;
v_____do__lift_3692_ = v_val_2645_;
v___y_3693_ = v___y_3732_;
v___y_3694_ = v___y_3733_;
v___y_3695_ = v___y_3734_;
v___y_3696_ = v___y_3735_;
v___y_3697_ = v___y_3736_;
v___y_3698_ = v___y_3737_;
v___y_3699_ = v___y_3738_;
v___y_3700_ = v___y_3739_;
v___y_3701_ = v___y_3740_;
v___y_3702_ = v___y_3741_;
goto v___jp_3685_;
}
else
{
lean_object* v___x_3747_; 
lean_inc(v_val_2645_);
v___x_3747_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_3686_ = v___y_3726_;
v___y_3687_ = v___y_3727_;
v___y_3688_ = v_a_3743_;
v___y_3689_ = v___y_3728_;
v___y_3690_ = v___y_3730_;
v___y_3691_ = v___y_3729_;
v_____do__lift_3692_ = v___x_3747_;
v___y_3693_ = v___y_3732_;
v___y_3694_ = v___y_3733_;
v___y_3695_ = v___y_3734_;
v___y_3696_ = v___y_3735_;
v___y_3697_ = v___y_3736_;
v___y_3698_ = v___y_3737_;
v___y_3699_ = v___y_3738_;
v___y_3700_ = v___y_3739_;
v___y_3701_ = v___y_3740_;
v___y_3702_ = v___y_3741_;
goto v___jp_3685_;
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_a_3743_);
lean_dec(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec(v___y_3726_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3748_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3744_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec(v___y_3726_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3756_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3742_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3742_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
v___jp_3764_:
{
lean_object* v___x_3780_; 
lean_inc(v___y_3766_);
lean_inc(v___y_3768_);
lean_inc_ref(v_type_2515_);
v___x_3780_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_____do__lift_3769_, v_type_2515_, v___y_3768_, v___y_3766_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l_Lean_leCarrierIsSort(v___y_3778_, v___y_3779_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; uint8_t v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3784_ = lean_unbox(v_a_3783_);
lean_dec(v_a_3783_);
if (v___x_3784_ == 0)
{
lean_inc(v_val_2645_);
v___y_3726_ = v_a_3781_;
v___y_3727_ = v___y_3765_;
v___y_3728_ = v___y_3766_;
v___y_3729_ = v___y_3768_;
v___y_3730_ = v___y_3767_;
v_____do__lift_3731_ = v_val_2645_;
v___y_3732_ = v___y_3770_;
v___y_3733_ = v___y_3771_;
v___y_3734_ = v___y_3772_;
v___y_3735_ = v___y_3773_;
v___y_3736_ = v___y_3774_;
v___y_3737_ = v___y_3775_;
v___y_3738_ = v___y_3776_;
v___y_3739_ = v___y_3777_;
v___y_3740_ = v___y_3778_;
v___y_3741_ = v___y_3779_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3785_; 
lean_inc(v_val_2645_);
v___x_3785_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_3726_ = v_a_3781_;
v___y_3727_ = v___y_3765_;
v___y_3728_ = v___y_3766_;
v___y_3729_ = v___y_3768_;
v___y_3730_ = v___y_3767_;
v_____do__lift_3731_ = v___x_3785_;
v___y_3732_ = v___y_3770_;
v___y_3733_ = v___y_3771_;
v___y_3734_ = v___y_3772_;
v___y_3735_ = v___y_3773_;
v___y_3736_ = v___y_3774_;
v___y_3737_ = v___y_3775_;
v___y_3738_ = v___y_3776_;
v___y_3739_ = v___y_3777_;
v___y_3740_ = v___y_3778_;
v___y_3741_ = v___y_3779_;
goto v___jp_3725_;
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v_a_3781_);
lean_dec(v___y_3768_);
lean_dec(v___y_3766_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3786_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3782_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3782_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v___y_3768_);
lean_dec(v___y_3766_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3794_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3780_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3780_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
v___jp_3802_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_3817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2515_);
v___x_3818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3817_, v_____do__lift_3805_, v_type_2515_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v___x_3820_ = l_Lean_leCarrierIsSort(v___y_3814_, v___y_3815_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; uint8_t v___x_3822_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3822_ = lean_unbox(v_a_3821_);
lean_dec(v_a_3821_);
if (v___x_3822_ == 0)
{
lean_inc(v_val_2645_);
v___y_3765_ = v___x_3816_;
v___y_3766_ = v___y_3803_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v_a_3819_;
v_____do__lift_3769_ = v_val_2645_;
v___y_3770_ = v___y_3806_;
v___y_3771_ = v___y_3807_;
v___y_3772_ = v___y_3808_;
v___y_3773_ = v___y_3809_;
v___y_3774_ = v___y_3810_;
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3823_; 
lean_inc(v_val_2645_);
v___x_3823_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_3765_ = v___x_3816_;
v___y_3766_ = v___y_3803_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v_a_3819_;
v_____do__lift_3769_ = v___x_3823_;
v___y_3770_ = v___y_3806_;
v___y_3771_ = v___y_3807_;
v___y_3772_ = v___y_3808_;
v___y_3773_ = v___y_3809_;
v___y_3774_ = v___y_3810_;
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
goto v___jp_3764_;
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3819_);
lean_dec(v___y_3803_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3824_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3820_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3820_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v___y_3803_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3832_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3818_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3818_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
v___jp_3840_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_type_2515_);
v___x_3854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3853_, v_____do__lift_3841_, v_type_2515_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = l_Lean_leCarrierIsSort(v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; uint8_t v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = lean_unbox(v_a_3857_);
lean_dec(v_a_3857_);
if (v___x_3858_ == 0)
{
lean_inc(v_val_2645_);
v___y_3803_ = v_a_3855_;
v___y_3804_ = v___x_3852_;
v_____do__lift_3805_ = v_val_2645_;
v___y_3806_ = v___y_3842_;
v___y_3807_ = v___y_3843_;
v___y_3808_ = v___y_3844_;
v___y_3809_ = v___y_3845_;
v___y_3810_ = v___y_3846_;
v___y_3811_ = v___y_3847_;
v___y_3812_ = v___y_3848_;
v___y_3813_ = v___y_3849_;
v___y_3814_ = v___y_3850_;
v___y_3815_ = v___y_3851_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3859_; 
lean_inc(v_val_2645_);
v___x_3859_ = l_Lean_Level_succ___override(v_val_2645_);
v___y_3803_ = v_a_3855_;
v___y_3804_ = v___x_3852_;
v_____do__lift_3805_ = v___x_3859_;
v___y_3806_ = v___y_3842_;
v___y_3807_ = v___y_3843_;
v___y_3808_ = v___y_3844_;
v___y_3809_ = v___y_3845_;
v___y_3810_ = v___y_3846_;
v___y_3811_ = v___y_3847_;
v___y_3812_ = v___y_3848_;
v___y_3813_ = v___y_3849_;
v___y_3814_ = v___y_3850_;
v___y_3815_ = v___y_3851_;
goto v___jp_3802_;
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_a_3855_);
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3860_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3856_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3856_);
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
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_del_object(v___x_2652_);
lean_dec(v_a_2650_);
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3868_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3854_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3854_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2647_);
lean_dec(v_val_2645_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
return v___x_2649_;
}
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_dec(v_a_2641_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v___x_3890_ = lean_box(0);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_3890_);
v___x_3892_ = v___x_2643_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec_ref(v___f_2639_);
lean_dec_ref(v_type_2515_);
v_a_3895_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_2640_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_2640_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___y_2528_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
v___jp_2531_:
{
if (lean_obj_tag(v___y_2533_) == 0)
{
lean_dec_ref_known(v___y_2533_, 1);
v___y_2528_ = v___y_2532_;
goto v___jp_2527_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v___y_2532_);
v_a_2534_ = lean_ctor_get(v___y_2533_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___y_2533_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___y_2533_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___y_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
v___jp_2542_:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2545_, v___y_2543_, v___y_2550_, v___y_2547_, v___y_2544_, v___y_2546_, v___y_2555_, v___y_2549_, v___y_2551_, v___y_2552_, v___y_2554_, v___y_2548_, v___y_2553_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2557_, v___y_2550_, v___y_2547_);
v___y_2532_ = v___y_2550_;
v___y_2533_ = v___x_2558_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v___y_2550_);
v_a_2559_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2556_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2556_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
v___jp_2567_:
{
if (lean_obj_tag(v___y_2581_) == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2580_);
lean_dec(v___y_2580_);
if (v___x_2583_ == 0)
{
lean_dec_ref(v___y_2570_);
v___y_2528_ = v___y_2575_;
goto v___jp_2527_;
}
else
{
v___y_2543_ = v___y_2568_;
v___y_2544_ = v___y_2569_;
v___y_2545_ = v___y_2570_;
v___y_2546_ = v___y_2571_;
v___y_2547_ = v___y_2572_;
v___y_2548_ = v___y_2573_;
v___y_2549_ = v___y_2574_;
v___y_2550_ = v___y_2575_;
v___y_2551_ = v___y_2576_;
v___y_2552_ = v___y_2577_;
v___y_2553_ = v___y_2578_;
v___y_2554_ = v___y_2579_;
v___y_2555_ = v___y_2582_;
goto v___jp_2542_;
}
}
else
{
lean_dec_ref_known(v___y_2581_, 1);
lean_dec(v___y_2580_);
v___y_2543_ = v___y_2568_;
v___y_2544_ = v___y_2569_;
v___y_2545_ = v___y_2570_;
v___y_2546_ = v___y_2571_;
v___y_2547_ = v___y_2572_;
v___y_2548_ = v___y_2573_;
v___y_2549_ = v___y_2574_;
v___y_2550_ = v___y_2575_;
v___y_2551_ = v___y_2576_;
v___y_2552_ = v___y_2577_;
v___y_2553_ = v___y_2578_;
v___y_2554_ = v___y_2579_;
v___y_2555_ = v___y_2582_;
goto v___jp_2542_;
}
}
v___jp_2584_:
{
if (v___y_2600_ == 0)
{
v___y_2568_ = v___y_2585_;
v___y_2569_ = v___y_2586_;
v___y_2570_ = v___y_2587_;
v___y_2571_ = v___y_2588_;
v___y_2572_ = v___y_2589_;
v___y_2573_ = v___y_2590_;
v___y_2574_ = v___y_2591_;
v___y_2575_ = v___y_2592_;
v___y_2576_ = v___y_2593_;
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2595_;
v___y_2579_ = v___y_2596_;
v___y_2580_ = v___y_2597_;
v___y_2581_ = v___y_2598_;
v___y_2582_ = v___y_2599_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2601_; 
lean_dec(v___y_2598_);
lean_dec(v___y_2597_);
v___x_2601_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2587_, v___y_2585_, v___y_2592_, v___y_2589_, v___y_2586_, v___y_2588_, v___y_2599_, v___y_2591_, v___y_2593_, v___y_2594_, v___y_2596_, v___y_2590_, v___y_2595_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_n(v_a_2602_, 2);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2602_, v___y_2592_, v___y_2589_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref_known(v___x_2603_, 1);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2602_, v___y_2592_, v___y_2589_);
v___y_2532_ = v___y_2592_;
v___y_2533_ = v___x_2604_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_a_2602_);
lean_dec(v___y_2592_);
v_a_2605_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2603_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2603_);
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
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___y_2592_);
v_a_2613_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2601_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2601_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
v___jp_2621_:
{
if (lean_obj_tag(v___y_2622_) == 0)
{
v___y_2585_ = v___y_2623_;
v___y_2586_ = v___y_2624_;
v___y_2587_ = v___y_2625_;
v___y_2588_ = v___y_2626_;
v___y_2589_ = v___y_2627_;
v___y_2590_ = v___y_2628_;
v___y_2591_ = v___y_2629_;
v___y_2592_ = v___y_2630_;
v___y_2593_ = v___y_2631_;
v___y_2594_ = v___y_2632_;
v___y_2595_ = v___y_2633_;
v___y_2596_ = v___y_2634_;
v___y_2597_ = v___y_2635_;
v___y_2598_ = v___y_2637_;
v___y_2599_ = v___y_2638_;
v___y_2600_ = v___y_2623_;
goto v___jp_2584_;
}
else
{
lean_dec_ref_known(v___y_2622_, 1);
v___y_2585_ = v___y_2623_;
v___y_2586_ = v___y_2624_;
v___y_2587_ = v___y_2625_;
v___y_2588_ = v___y_2626_;
v___y_2589_ = v___y_2627_;
v___y_2590_ = v___y_2628_;
v___y_2591_ = v___y_2629_;
v___y_2592_ = v___y_2630_;
v___y_2593_ = v___y_2631_;
v___y_2594_ = v___y_2632_;
v___y_2595_ = v___y_2633_;
v___y_2596_ = v___y_2634_;
v___y_2597_ = v___y_2635_;
v___y_2598_ = v___y_2637_;
v___y_2599_ = v___y_2638_;
v___y_2600_ = v___y_2636_;
goto v___jp_2584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec(v_a_3904_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3917_, v_x_3918_, v_x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3921_, lean_object* v_x_3922_, size_t v_x_3923_, size_t v_x_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3922_, v_x_3923_, v_x_3924_, v_x_3925_, v_x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_, lean_object* v_x_3931_, lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
size_t v_x_730331__boxed_3934_; size_t v_x_730332__boxed_3935_; lean_object* v_res_3936_; 
v_x_730331__boxed_3934_ = lean_unbox_usize(v_x_3930_);
lean_dec(v_x_3930_);
v_x_730332__boxed_3935_ = lean_unbox_usize(v_x_3931_);
lean_dec(v_x_3931_);
v_res_3936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3928_, v_x_3929_, v_x_730331__boxed_3934_, v_x_730332__boxed_3935_, v_x_3932_, v_x_3933_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3937_, lean_object* v_n_3938_, lean_object* v_k_3939_, lean_object* v_v_3940_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3938_, v_k_3939_, v_v_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3942_, size_t v_depth_3943_, lean_object* v_keys_3944_, lean_object* v_vals_3945_, lean_object* v_heq_3946_, lean_object* v_i_3947_, lean_object* v_entries_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3943_, v_keys_3944_, v_vals_3945_, v_i_3947_, v_entries_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3950_, lean_object* v_depth_3951_, lean_object* v_keys_3952_, lean_object* v_vals_3953_, lean_object* v_heq_3954_, lean_object* v_i_3955_, lean_object* v_entries_3956_){
_start:
{
size_t v_depth_boxed_3957_; lean_object* v_res_3958_; 
v_depth_boxed_3957_ = lean_unbox_usize(v_depth_3951_);
lean_dec(v_depth_3951_);
v_res_3958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3950_, v_depth_boxed_3957_, v_keys_3952_, v_vals_3953_, v_heq_3954_, v_i_3955_, v_entries_3956_);
lean_dec_ref(v_vals_3953_);
lean_dec_ref(v_keys_3952_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3959_, lean_object* v_x_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3960_, v_x_3961_, v_x_3962_, v_x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3965_, lean_object* v_base_3966_, lean_object* v_natModuleInst_3967_, lean_object* v_declName_3968_, lean_object* v_le_3969_, lean_object* v_mid_3970_, lean_object* v_ord_3971_){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = lean_box(0);
v___x_3973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3973_, 0, v_val_3965_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_mkConst(v_declName_3968_, v___x_3973_);
v___x_3975_ = l_Lean_mkApp5(v___x_3974_, v_base_3966_, v_natModuleInst_3967_, v_le_3969_, v_mid_3970_, v_ord_3971_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_4078_, lean_object* v_base_4079_, lean_object* v_natModuleInst_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4092_; 
lean_inc_ref(v_base_4079_);
v___x_4092_ = l_Lean_Meta_getDecLevel_x3f(v_base_4079_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_5149_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_5149_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_5149_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
if (lean_obj_tag(v_a_4093_) == 1)
{
lean_object* v_val_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_5144_; 
lean_del_object(v___x_4095_);
v_val_4097_ = lean_ctor_get(v_a_4093_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v_a_4093_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_4099_ = v_a_4093_;
v_isShared_4100_ = v_isSharedCheck_5144_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_val_4097_);
lean_dec(v_a_4093_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_5144_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v_a_4121_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v_leLvl_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v_____do__lift_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v_____do__lift_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v_noNatDivInstQ_x3f_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v_isLinearInstQ_x3f_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; lean_object* v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4830_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v_____do__lift_4840_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v___y_4877_; lean_object* v___y_4878_; lean_object* v___y_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v___y_4884_; lean_object* v___y_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4916_; lean_object* v_lawfulOrderLTLvl_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___y_4924_; lean_object* v___y_4925_; lean_object* v___y_4926_; lean_object* v___y_4927_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v___y_4940_; lean_object* v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; lean_object* v___y_4950_; lean_object* v___y_4951_; lean_object* v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v_____do__lift_5017_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; lean_object* v___y_5027_; lean_object* v_____do__lift_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_leCarrierIsSort(v_a_4089_, v_a_4090_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; uint8_t v___x_5134_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5134_ = lean_unbox(v_a_5133_);
lean_dec(v_a_5133_);
if (v___x_5134_ == 0)
{
lean_inc(v_val_4097_);
v_____do__lift_5097_ = v_val_4097_;
v___y_5098_ = v_a_4081_;
v___y_5099_ = v_a_4082_;
v___y_5100_ = v_a_4083_;
v___y_5101_ = v_a_4084_;
v___y_5102_ = v_a_4085_;
v___y_5103_ = v_a_4086_;
v___y_5104_ = v_a_4087_;
v___y_5105_ = v_a_4088_;
v___y_5106_ = v_a_4089_;
v___y_5107_ = v_a_4090_;
goto v___jp_5096_;
}
else
{
lean_object* v___x_5135_; 
lean_inc(v_val_4097_);
v___x_5135_ = l_Lean_Level_succ___override(v_val_4097_);
v_____do__lift_5097_ = v___x_5135_;
v___y_5098_ = v_a_4081_;
v___y_5099_ = v_a_4082_;
v___y_5100_ = v_a_4083_;
v___y_5101_ = v_a_4084_;
v___y_5102_ = v_a_4085_;
v___y_5103_ = v_a_4086_;
v___y_5104_ = v_a_4087_;
v___y_5105_ = v_a_4088_;
v___y_5106_ = v_a_4089_;
v___y_5107_ = v_a_4090_;
goto v___jp_5096_;
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5136_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5132_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5132_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
v___jp_4101_:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4111_, v___y_4115_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v_structs_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v_structs_4124_ = lean_ctor_get(v_a_4123_, 0);
lean_inc_ref(v_structs_4124_);
lean_dec(v_a_4123_);
v___x_4125_ = lean_array_get_size(v_structs_4124_);
lean_dec_ref(v_structs_4124_);
v___x_4126_ = lean_box(0);
lean_inc_ref(v___y_4119_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___y_4119_);
v___x_4128_ = v___x_4099_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___y_4119_);
v___x_4128_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___f_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_inc_ref(v___y_4107_);
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___y_4107_);
v___x_4130_ = lean_unsigned_to_nat(32u);
v___x_4131_ = lean_mk_empty_array_with_capacity(v___x_4130_);
v___x_4132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__0);
v___x_4133_ = ((size_t)5ULL);
lean_inc(v___y_4114_);
v___x_4134_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4131_);
lean_ctor_set(v___x_4134_, 2, v___y_4114_);
lean_ctor_set(v___x_4134_, 3, v___y_4114_);
lean_ctor_set_usize(v___x_4134_, 4, v___x_4133_);
v___x_4135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__2);
v___x_4136_ = 0;
v___x_4137_ = lean_box(0);
lean_inc_ref_n(v___x_4134_, 7);
v___x_4138_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_4138_, 0, v___x_4125_);
lean_ctor_set(v___x_4138_, 1, v___x_4126_);
lean_ctor_set(v___x_4138_, 2, v_type_4078_);
lean_ctor_set(v___x_4138_, 3, v_val_4097_);
lean_ctor_set(v___x_4138_, 4, v___y_4120_);
lean_ctor_set(v___x_4138_, 5, v___y_4117_);
lean_ctor_set(v___x_4138_, 6, v___y_4113_);
lean_ctor_set(v___x_4138_, 7, v___y_4108_);
lean_ctor_set(v___x_4138_, 8, v___y_4104_);
lean_ctor_set(v___x_4138_, 9, v___y_4112_);
lean_ctor_set(v___x_4138_, 10, v___y_4105_);
lean_ctor_set(v___x_4138_, 11, v___y_4118_);
lean_ctor_set(v___x_4138_, 12, v___x_4126_);
lean_ctor_set(v___x_4138_, 13, v___x_4126_);
lean_ctor_set(v___x_4138_, 14, v___x_4126_);
lean_ctor_set(v___x_4138_, 15, v___x_4126_);
lean_ctor_set(v___x_4138_, 16, v___x_4126_);
lean_ctor_set(v___x_4138_, 17, v___y_4110_);
lean_ctor_set(v___x_4138_, 18, v___y_4102_);
lean_ctor_set(v___x_4138_, 19, v___x_4126_);
lean_ctor_set(v___x_4138_, 20, v___y_4116_);
lean_ctor_set(v___x_4138_, 21, v_a_4121_);
lean_ctor_set(v___x_4138_, 22, v___y_4103_);
lean_ctor_set(v___x_4138_, 23, v___y_4119_);
lean_ctor_set(v___x_4138_, 24, v___y_4107_);
lean_ctor_set(v___x_4138_, 25, v___x_4128_);
lean_ctor_set(v___x_4138_, 26, v___x_4129_);
lean_ctor_set(v___x_4138_, 27, v___x_4126_);
lean_ctor_set(v___x_4138_, 28, v___y_4106_);
lean_ctor_set(v___x_4138_, 29, v___y_4109_);
lean_ctor_set(v___x_4138_, 30, v___x_4134_);
lean_ctor_set(v___x_4138_, 31, v___x_4135_);
lean_ctor_set(v___x_4138_, 32, v___x_4134_);
lean_ctor_set(v___x_4138_, 33, v___x_4134_);
lean_ctor_set(v___x_4138_, 34, v___x_4134_);
lean_ctor_set(v___x_4138_, 35, v___x_4134_);
lean_ctor_set(v___x_4138_, 36, v___x_4126_);
lean_ctor_set(v___x_4138_, 37, v___x_4135_);
lean_ctor_set(v___x_4138_, 38, v___x_4134_);
lean_ctor_set(v___x_4138_, 39, v___x_4137_);
lean_ctor_set(v___x_4138_, 40, v___x_4134_);
lean_ctor_set(v___x_4138_, 41, v___x_4134_);
lean_ctor_set_uint8(v___x_4138_, sizeof(void*)*42, v___x_4136_);
v___f_4139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2), 2, 1);
lean_closure_set(v___f_4139_, 0, v___x_4138_);
v___x_4140_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4141_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4140_, v___f_4139_, v___y_4111_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4149_; 
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4149_ == 0)
{
lean_object* v_unused_4150_; 
v_unused_4150_ = lean_ctor_get(v___x_4141_, 0);
lean_dec(v_unused_4150_);
v___x_4143_ = v___x_4141_;
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
else
{
lean_dec(v___x_4141_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4125_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4145_);
v___x_4147_ = v___x_4143_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
v_a_4151_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4141_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4141_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_a_4121_);
lean_dec_ref(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4160_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4122_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4122_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
v___jp_4168_:
{
if (lean_obj_tag(v___y_4189_) == 0)
{
lean_dec(v___y_4177_);
v___y_4102_ = v___y_4169_;
v___y_4103_ = v___y_4170_;
v___y_4104_ = v___y_4171_;
v___y_4105_ = v___y_4184_;
v___y_4106_ = v___y_4174_;
v___y_4107_ = v___y_4175_;
v___y_4108_ = v___y_4187_;
v___y_4109_ = v___y_4176_;
v___y_4110_ = v___y_4178_;
v___y_4111_ = v___y_4179_;
v___y_4112_ = v___y_4180_;
v___y_4113_ = v___y_4189_;
v___y_4114_ = v___y_4181_;
v___y_4115_ = v___y_4190_;
v___y_4116_ = v_a_4194_;
v___y_4117_ = v___y_4191_;
v___y_4118_ = v___y_4192_;
v___y_4119_ = v___y_4183_;
v___y_4120_ = v___y_4193_;
v_a_4121_ = v___y_4189_;
goto v___jp_4101_;
}
else
{
lean_object* v_val_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_val_4195_ = lean_ctor_get(v___y_4189_, 0);
v___x_4196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__0));
lean_inc(v___y_4172_);
v___x_4197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___y_4177_);
lean_ctor_set(v___x_4197_, 1, v___y_4172_);
v___x_4198_ = l_Lean_mkConst(v___x_4196_, v___x_4197_);
lean_inc(v_val_4195_);
lean_inc_ref(v_type_4078_);
v___x_4199_ = l_Lean_mkAppB(v___x_4198_, v_type_4078_, v_val_4195_);
v___x_4200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4199_, v___y_4173_, v___y_4182_, v___y_4186_, v___y_4188_, v___y_4190_, v___y_4185_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4202_, 0, v_a_4201_);
v___y_4102_ = v___y_4169_;
v___y_4103_ = v___y_4170_;
v___y_4104_ = v___y_4171_;
v___y_4105_ = v___y_4184_;
v___y_4106_ = v___y_4174_;
v___y_4107_ = v___y_4175_;
v___y_4108_ = v___y_4187_;
v___y_4109_ = v___y_4176_;
v___y_4110_ = v___y_4178_;
v___y_4111_ = v___y_4179_;
v___y_4112_ = v___y_4180_;
v___y_4113_ = v___y_4189_;
v___y_4114_ = v___y_4181_;
v___y_4115_ = v___y_4190_;
v___y_4116_ = v_a_4194_;
v___y_4117_ = v___y_4191_;
v___y_4118_ = v___y_4192_;
v___y_4119_ = v___y_4183_;
v___y_4120_ = v___y_4193_;
v_a_4121_ = v___x_4202_;
goto v___jp_4101_;
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref_known(v___y_4189_, 1);
lean_dec(v_a_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec(v___y_4187_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4178_);
lean_dec_ref(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4203_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4200_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4200_);
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
}
v___jp_4211_:
{
if (lean_obj_tag(v___y_4226_) == 0)
{
v___y_4169_ = v___y_4212_;
v___y_4170_ = v___y_4214_;
v___y_4171_ = v___y_4215_;
v___y_4172_ = v___y_4216_;
v___y_4173_ = v___y_4232_;
v___y_4174_ = v___y_4218_;
v___y_4175_ = v___y_4219_;
v___y_4176_ = v___y_4221_;
v___y_4177_ = v_leLvl_4230_;
v___y_4178_ = v___y_4222_;
v___y_4179_ = v___y_4231_;
v___y_4180_ = v___y_4223_;
v___y_4181_ = v___y_4225_;
v___y_4182_ = v___y_4233_;
v___y_4183_ = v___y_4229_;
v___y_4184_ = v___y_4217_;
v___y_4185_ = v___y_4237_;
v___y_4186_ = v___y_4234_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v___y_4235_;
v___y_4189_ = v___y_4224_;
v___y_4190_ = v___y_4236_;
v___y_4191_ = v___y_4226_;
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4228_;
v_a_4194_ = v___y_4226_;
goto v___jp_4168_;
}
else
{
lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v_val_4238_ = lean_ctor_get(v___y_4226_, 0);
v___x_4239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v___y_4213_);
v___x_4240_ = l_Lean_Name_mkStr2(v___y_4213_, v___x_4239_);
lean_inc(v___y_4216_);
lean_inc(v_leLvl_4230_);
v___x_4241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4241_, 0, v_leLvl_4230_);
lean_ctor_set(v___x_4241_, 1, v___y_4216_);
v___x_4242_ = l_Lean_mkConst(v___x_4240_, v___x_4241_);
lean_inc(v_val_4238_);
lean_inc_ref(v_type_4078_);
v___x_4243_ = l_Lean_mkAppB(v___x_4242_, v_type_4078_, v_val_4238_);
v___x_4244_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4243_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___x_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_a_4245_);
v___y_4169_ = v___y_4212_;
v___y_4170_ = v___y_4214_;
v___y_4171_ = v___y_4215_;
v___y_4172_ = v___y_4216_;
v___y_4173_ = v___y_4232_;
v___y_4174_ = v___y_4218_;
v___y_4175_ = v___y_4219_;
v___y_4176_ = v___y_4221_;
v___y_4177_ = v_leLvl_4230_;
v___y_4178_ = v___y_4222_;
v___y_4179_ = v___y_4231_;
v___y_4180_ = v___y_4223_;
v___y_4181_ = v___y_4225_;
v___y_4182_ = v___y_4233_;
v___y_4183_ = v___y_4229_;
v___y_4184_ = v___y_4217_;
v___y_4185_ = v___y_4237_;
v___y_4186_ = v___y_4234_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v___y_4235_;
v___y_4189_ = v___y_4224_;
v___y_4190_ = v___y_4236_;
v___y_4191_ = v___y_4226_;
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4228_;
v_a_4194_ = v___x_4246_;
goto v___jp_4168_;
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref_known(v___y_4226_, 1);
lean_dec(v_leLvl_4230_);
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v___y_4212_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4247_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4244_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4244_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
}
v___jp_4255_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__11));
lean_inc_ref(v___y_4279_);
v___x_4297_ = l_Lean_Name_mkStr2(v___y_4279_, v___x_4296_);
lean_inc(v___y_4282_);
v___x_4298_ = l_Lean_mkConst(v___x_4297_, v___y_4282_);
lean_inc_ref(v_type_4078_);
v___x_4299_ = l_Lean_mkAppB(v___x_4298_, v_type_4078_, v___y_4281_);
v___x_4300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4299_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc_ref(v___y_4263_);
v___x_4303_ = l_Lean_Name_mkStr2(v___y_4263_, v___x_4302_);
lean_inc(v___y_4282_);
v___x_4304_ = l_Lean_mkConst(v___x_4303_, v___y_4282_);
lean_inc_ref(v_type_4078_);
v___x_4305_ = l_Lean_mkApp3(v___x_4304_, v_type_4078_, v___y_4267_, v___y_4268_);
v___x_4306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4305_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__57));
lean_inc_ref(v___y_4270_);
v___x_4309_ = l_Lean_Name_mkStr2(v___y_4270_, v___x_4308_);
lean_inc(v___y_4261_);
v___x_4310_ = l_Lean_mkConst(v___x_4309_, v___y_4261_);
lean_inc_ref_n(v_type_4078_, 3);
v___x_4311_ = l_Lean_mkApp4(v___x_4310_, v_type_4078_, v_type_4078_, v_type_4078_, v___y_4274_);
v___x_4312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4311_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_4256_);
v___x_4315_ = l_Lean_Name_mkStr2(v___y_4256_, v___x_4314_);
v___x_4316_ = l_Lean_mkConst(v___x_4315_, v___y_4261_);
lean_inc_ref_n(v_type_4078_, 3);
v___x_4317_ = l_Lean_mkApp4(v___x_4316_, v_type_4078_, v_type_4078_, v_type_4078_, v___y_4273_);
v___x_4318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4317_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_4278_);
v___x_4321_ = l_Lean_Name_mkStr2(v___y_4278_, v___x_4320_);
v___x_4322_ = l_Lean_mkConst(v___x_4321_, v___y_4282_);
lean_inc_ref(v_type_4078_);
v___x_4323_ = l_Lean_mkAppB(v___x_4322_, v_type_4078_, v___y_4277_);
v___x_4324_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4323_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_4275_);
v___x_4327_ = l_Lean_Name_mkStr2(v___y_4275_, v___x_4326_);
v___x_4328_ = l_Lean_mkConst(v___x_4327_, v___y_4260_);
lean_inc_ref_n(v_type_4078_, 2);
lean_inc_ref(v___x_4328_);
v___x_4329_ = l_Lean_mkApp4(v___x_4328_, v___y_4266_, v_type_4078_, v_type_4078_, v___y_4269_);
v___x_4330_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4329_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
lean_inc_ref_n(v_type_4078_, 2);
v___x_4332_ = l_Lean_mkApp4(v___x_4328_, v___y_4262_, v_type_4078_, v_type_4078_, v___y_4257_);
v___x_4333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4332_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = l_Lean_leCarrierIsSort(v___y_4294_, v___y_4295_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; uint8_t v___x_4337_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = lean_unbox(v_a_4336_);
lean_dec(v_a_4336_);
if (v___x_4337_ == 0)
{
lean_inc(v_val_4097_);
v___y_4212_ = v_a_4307_;
v___y_4213_ = v___y_4271_;
v___y_4214_ = v_a_4313_;
v___y_4215_ = v___y_4258_;
v___y_4216_ = v___y_4259_;
v___y_4217_ = v___y_4272_;
v___y_4218_ = v_a_4319_;
v___y_4219_ = v_a_4334_;
v___y_4220_ = v___y_4276_;
v___y_4221_ = v_a_4325_;
v___y_4222_ = v_a_4301_;
v___y_4223_ = v___y_4264_;
v___y_4224_ = v___y_4280_;
v___y_4225_ = v___y_4265_;
v___y_4226_ = v___y_4283_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___y_4285_;
v___y_4229_ = v_a_4331_;
v_leLvl_4230_ = v_val_4097_;
v___y_4231_ = v___y_4286_;
v___y_4232_ = v___y_4290_;
v___y_4233_ = v___y_4291_;
v___y_4234_ = v___y_4292_;
v___y_4235_ = v___y_4293_;
v___y_4236_ = v___y_4294_;
v___y_4237_ = v___y_4295_;
goto v___jp_4211_;
}
else
{
lean_object* v___x_4338_; 
lean_inc(v_val_4097_);
v___x_4338_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_4212_ = v_a_4307_;
v___y_4213_ = v___y_4271_;
v___y_4214_ = v_a_4313_;
v___y_4215_ = v___y_4258_;
v___y_4216_ = v___y_4259_;
v___y_4217_ = v___y_4272_;
v___y_4218_ = v_a_4319_;
v___y_4219_ = v_a_4334_;
v___y_4220_ = v___y_4276_;
v___y_4221_ = v_a_4325_;
v___y_4222_ = v_a_4301_;
v___y_4223_ = v___y_4264_;
v___y_4224_ = v___y_4280_;
v___y_4225_ = v___y_4265_;
v___y_4226_ = v___y_4283_;
v___y_4227_ = v___y_4284_;
v___y_4228_ = v___y_4285_;
v___y_4229_ = v_a_4331_;
v_leLvl_4230_ = v___x_4338_;
v___y_4231_ = v___y_4286_;
v___y_4232_ = v___y_4290_;
v___y_4233_ = v___y_4291_;
v___y_4234_ = v___y_4292_;
v___y_4235_ = v___y_4293_;
v___y_4236_ = v___y_4294_;
v___y_4237_ = v___y_4295_;
goto v___jp_4211_;
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_a_4334_);
lean_dec(v_a_4331_);
lean_dec(v_a_4325_);
lean_dec(v_a_4319_);
lean_dec(v_a_4313_);
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4280_);
lean_dec(v___y_4276_);
lean_dec(v___y_4272_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec(v___y_4258_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4339_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4335_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4335_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_a_4331_);
lean_dec(v_a_4325_);
lean_dec(v_a_4319_);
lean_dec(v_a_4313_);
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4280_);
lean_dec(v___y_4276_);
lean_dec(v___y_4272_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec(v___y_4258_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4347_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4333_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4333_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v___x_4328_);
lean_dec(v_a_4325_);
lean_dec(v_a_4319_);
lean_dec(v_a_4313_);
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4280_);
lean_dec(v___y_4276_);
lean_dec(v___y_4272_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4355_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4330_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4330_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_a_4319_);
lean_dec(v_a_4313_);
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4280_);
lean_dec(v___y_4276_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4260_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4363_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4324_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4324_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_a_4313_);
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4260_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4371_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4318_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4318_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_a_4307_);
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4379_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4312_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4312_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_a_4301_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4387_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4306_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4306_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4395_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4300_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4300_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
v___jp_4403_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4407_);
v___x_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_____do__lift_4435_);
lean_ctor_set(v___x_4447_, 1, v___y_4407_);
v___x_4448_ = l_Lean_mkConst(v___x_4446_, v___x_4447_);
lean_inc_ref(v_type_4078_);
v___x_4449_ = l_Lean_Expr_app___override(v___x_4448_, v_type_4078_);
v___x_4450_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4449_, v___y_4431_, v___y_4441_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_dec_ref_known(v___x_4450_, 1);
v___y_4256_ = v___y_4404_;
v___y_4257_ = v___y_4406_;
v___y_4258_ = v___y_4405_;
v___y_4259_ = v___y_4407_;
v___y_4260_ = v___y_4408_;
v___y_4261_ = v___y_4409_;
v___y_4262_ = v___y_4410_;
v___y_4263_ = v___y_4412_;
v___y_4264_ = v___y_4411_;
v___y_4265_ = v___y_4413_;
v___y_4266_ = v___y_4414_;
v___y_4267_ = v___y_4415_;
v___y_4268_ = v___y_4416_;
v___y_4269_ = v___y_4417_;
v___y_4270_ = v___y_4418_;
v___y_4271_ = v___y_4419_;
v___y_4272_ = v___y_4420_;
v___y_4273_ = v___y_4421_;
v___y_4274_ = v___y_4422_;
v___y_4275_ = v___y_4423_;
v___y_4276_ = v___y_4424_;
v___y_4277_ = v___y_4425_;
v___y_4278_ = v___y_4426_;
v___y_4279_ = v___y_4427_;
v___y_4280_ = v___y_4428_;
v___y_4281_ = v___y_4429_;
v___y_4282_ = v___y_4430_;
v___y_4283_ = v___y_4432_;
v___y_4284_ = v___y_4433_;
v___y_4285_ = v___y_4434_;
v___y_4286_ = v___y_4436_;
v___y_4287_ = v___y_4437_;
v___y_4288_ = v___y_4438_;
v___y_4289_ = v___y_4439_;
v___y_4290_ = v___y_4440_;
v___y_4291_ = v___y_4441_;
v___y_4292_ = v___y_4442_;
v___y_4293_ = v___y_4443_;
v___y_4294_ = v___y_4444_;
v___y_4295_ = v___y_4445_;
goto v___jp_4255_;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
v___jp_4459_:
{
if (lean_obj_tag(v___y_4484_) == 1)
{
lean_object* v_val_4500_; lean_object* v___x_4501_; 
v_val_4500_ = lean_ctor_get(v___y_4484_, 0);
lean_inc(v_val_4500_);
v___x_4501_ = l_Lean_leCarrierIsSort(v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; uint8_t v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = lean_unbox(v_a_4502_);
lean_dec(v_a_4502_);
if (v___x_4503_ == 0)
{
lean_inc(v_val_4097_);
v___y_4404_ = v___y_4460_;
v___y_4405_ = v___y_4462_;
v___y_4406_ = v___y_4461_;
v___y_4407_ = v___y_4463_;
v___y_4408_ = v___y_4464_;
v___y_4409_ = v___y_4465_;
v___y_4410_ = v___y_4466_;
v___y_4411_ = v___y_4468_;
v___y_4412_ = v___y_4467_;
v___y_4413_ = v___y_4469_;
v___y_4414_ = v___y_4470_;
v___y_4415_ = v___y_4471_;
v___y_4416_ = v___y_4472_;
v___y_4417_ = v___y_4473_;
v___y_4418_ = v___y_4474_;
v___y_4419_ = v___y_4475_;
v___y_4420_ = v___y_4476_;
v___y_4421_ = v___y_4477_;
v___y_4422_ = v___y_4478_;
v___y_4423_ = v___y_4479_;
v___y_4424_ = v___y_4480_;
v___y_4425_ = v___y_4481_;
v___y_4426_ = v___y_4482_;
v___y_4427_ = v___y_4483_;
v___y_4428_ = v___y_4484_;
v___y_4429_ = v___y_4485_;
v___y_4430_ = v___y_4486_;
v___y_4431_ = v_val_4500_;
v___y_4432_ = v___y_4487_;
v___y_4433_ = v___y_4488_;
v___y_4434_ = v___y_4489_;
v_____do__lift_4435_ = v_val_4097_;
v___y_4436_ = v___y_4490_;
v___y_4437_ = v___y_4491_;
v___y_4438_ = v___y_4492_;
v___y_4439_ = v___y_4493_;
v___y_4440_ = v___y_4494_;
v___y_4441_ = v___y_4495_;
v___y_4442_ = v___y_4496_;
v___y_4443_ = v___y_4497_;
v___y_4444_ = v___y_4498_;
v___y_4445_ = v___y_4499_;
goto v___jp_4403_;
}
else
{
lean_object* v___x_4504_; 
lean_inc(v_val_4097_);
v___x_4504_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_4404_ = v___y_4460_;
v___y_4405_ = v___y_4462_;
v___y_4406_ = v___y_4461_;
v___y_4407_ = v___y_4463_;
v___y_4408_ = v___y_4464_;
v___y_4409_ = v___y_4465_;
v___y_4410_ = v___y_4466_;
v___y_4411_ = v___y_4468_;
v___y_4412_ = v___y_4467_;
v___y_4413_ = v___y_4469_;
v___y_4414_ = v___y_4470_;
v___y_4415_ = v___y_4471_;
v___y_4416_ = v___y_4472_;
v___y_4417_ = v___y_4473_;
v___y_4418_ = v___y_4474_;
v___y_4419_ = v___y_4475_;
v___y_4420_ = v___y_4476_;
v___y_4421_ = v___y_4477_;
v___y_4422_ = v___y_4478_;
v___y_4423_ = v___y_4479_;
v___y_4424_ = v___y_4480_;
v___y_4425_ = v___y_4481_;
v___y_4426_ = v___y_4482_;
v___y_4427_ = v___y_4483_;
v___y_4428_ = v___y_4484_;
v___y_4429_ = v___y_4485_;
v___y_4430_ = v___y_4486_;
v___y_4431_ = v_val_4500_;
v___y_4432_ = v___y_4487_;
v___y_4433_ = v___y_4488_;
v___y_4434_ = v___y_4489_;
v_____do__lift_4435_ = v___x_4504_;
v___y_4436_ = v___y_4490_;
v___y_4437_ = v___y_4491_;
v___y_4438_ = v___y_4492_;
v___y_4439_ = v___y_4493_;
v___y_4440_ = v___y_4494_;
v___y_4441_ = v___y_4495_;
v___y_4442_ = v___y_4496_;
v___y_4443_ = v___y_4497_;
v___y_4444_ = v___y_4498_;
v___y_4445_ = v___y_4499_;
goto v___jp_4403_;
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec_ref_known(v___y_4484_, 1);
lean_dec(v_val_4500_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4505_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4501_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4501_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
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
v___y_4285_ = v___y_4489_;
v___y_4286_ = v___y_4490_;
v___y_4287_ = v___y_4491_;
v___y_4288_ = v___y_4492_;
v___y_4289_ = v___y_4493_;
v___y_4290_ = v___y_4494_;
v___y_4291_ = v___y_4495_;
v___y_4292_ = v___y_4496_;
v___y_4293_ = v___y_4497_;
v___y_4294_ = v___y_4498_;
v___y_4295_ = v___y_4499_;
goto v___jp_4255_;
}
}
v___jp_4513_:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_inc(v___y_4517_);
v___x_4557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4557_, 0, v_____do__lift_4546_);
lean_ctor_set(v___x_4557_, 1, v___y_4517_);
v___x_4558_ = l_Lean_mkConst(v___y_4521_, v___x_4557_);
lean_inc_ref(v_type_4078_);
v___x_4559_ = l_Lean_Expr_app___override(v___x_4558_, v_type_4078_);
v___x_4560_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4559_, v___y_4543_, v___y_4552_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_dec_ref_known(v___x_4560_, 1);
v___y_4460_ = v___y_4514_;
v___y_4461_ = v___y_4516_;
v___y_4462_ = v___y_4515_;
v___y_4463_ = v___y_4517_;
v___y_4464_ = v___y_4518_;
v___y_4465_ = v___y_4519_;
v___y_4466_ = v___y_4520_;
v___y_4467_ = v___y_4523_;
v___y_4468_ = v___y_4522_;
v___y_4469_ = v___y_4524_;
v___y_4470_ = v___y_4525_;
v___y_4471_ = v___y_4526_;
v___y_4472_ = v___y_4527_;
v___y_4473_ = v___y_4528_;
v___y_4474_ = v___y_4529_;
v___y_4475_ = v___y_4530_;
v___y_4476_ = v___y_4531_;
v___y_4477_ = v___y_4532_;
v___y_4478_ = v___y_4533_;
v___y_4479_ = v___y_4534_;
v___y_4480_ = v___y_4535_;
v___y_4481_ = v___y_4536_;
v___y_4482_ = v___y_4537_;
v___y_4483_ = v___y_4538_;
v___y_4484_ = v___y_4539_;
v___y_4485_ = v___y_4540_;
v___y_4486_ = v___y_4541_;
v___y_4487_ = v___y_4542_;
v___y_4488_ = v___y_4544_;
v___y_4489_ = v___y_4545_;
v___y_4490_ = v___y_4547_;
v___y_4491_ = v___y_4548_;
v___y_4492_ = v___y_4549_;
v___y_4493_ = v___y_4550_;
v___y_4494_ = v___y_4551_;
v___y_4495_ = v___y_4552_;
v___y_4496_ = v___y_4553_;
v___y_4497_ = v___y_4554_;
v___y_4498_ = v___y_4555_;
v___y_4499_ = v___y_4556_;
goto v___jp_4459_;
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
v___jp_4569_:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
lean_inc_n(v___y_4578_, 14);
v___x_4592_ = l_Lean_mkConst(v___x_4591_, v___y_4578_);
v___x_4593_ = l_Lean_mkAppB(v___x_4592_, v_base_4079_, v_natModuleInst_4080_);
v___x_4594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__49));
v___x_4595_ = l_Lean_mkConst(v___x_4594_, v___y_4578_);
lean_inc_ref_n(v___x_4593_, 4);
lean_inc_ref_n(v_type_4078_, 14);
v___x_4596_ = l_Lean_mkAppB(v___x_4595_, v_type_4078_, v___x_4593_);
v___x_4597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__52));
v___x_4598_ = l_Lean_mkConst(v___x_4597_, v___y_4578_);
lean_inc_ref_n(v___x_4596_, 2);
v___x_4599_ = l_Lean_mkAppB(v___x_4598_, v_type_4078_, v___x_4596_);
v___x_4600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__4));
v___x_4601_ = l_Lean_mkConst(v___x_4600_, v___y_4578_);
lean_inc_ref(v___x_4599_);
v___x_4602_ = l_Lean_mkAppB(v___x_4601_, v_type_4078_, v___x_4599_);
v___x_4603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__9));
v___x_4604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4605_ = l_Lean_mkConst(v___x_4604_, v___y_4578_);
lean_inc_ref(v___x_4602_);
v___x_4606_ = l_Lean_mkAppB(v___x_4605_, v_type_4078_, v___x_4602_);
v___x_4607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_4608_ = l_Lean_mkConst(v___x_4607_, v___y_4578_);
v___x_4609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4610_ = l_Lean_mkConst(v___x_4609_, v___y_4578_);
v___x_4611_ = l_Lean_mkAppB(v___x_4610_, v_type_4078_, v___x_4599_);
v___x_4612_ = l_Lean_mkAppB(v___x_4608_, v_type_4078_, v___x_4611_);
v___x_4613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__33));
v___x_4614_ = l_Lean_mkConst(v___x_4613_, v___y_4578_);
v___x_4615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4616_ = l_Lean_mkConst(v___x_4615_, v___y_4578_);
v___x_4617_ = l_Lean_mkAppB(v___x_4616_, v_type_4078_, v___x_4596_);
v___x_4618_ = l_Lean_mkAppB(v___x_4614_, v_type_4078_, v___x_4617_);
v___x_4619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4620_ = l_Lean_mkConst(v___x_4619_, v___y_4578_);
v___x_4621_ = l_Lean_mkAppB(v___x_4620_, v_type_4078_, v___x_4596_);
v___x_4622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4623_ = lean_unsigned_to_nat(0u);
v___x_4624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
lean_ctor_set(v___x_4625_, 1, v___y_4578_);
v___x_4626_ = l_Lean_mkConst(v___x_4622_, v___x_4625_);
v___x_4627_ = l_Lean_Int_mkType;
v___x_4628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4629_ = l_Lean_mkConst(v___x_4628_, v___y_4578_);
v___x_4630_ = l_Lean_mkAppB(v___x_4629_, v_type_4078_, v___x_4593_);
lean_inc_ref(v___x_4626_);
v___x_4631_ = l_Lean_mkApp3(v___x_4626_, v___x_4627_, v_type_4078_, v___x_4630_);
v___x_4632_ = l_Lean_Nat_mkType;
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__11));
v___x_4634_ = l_Lean_mkConst(v___x_4633_, v___y_4578_);
v___x_4635_ = l_Lean_mkAppB(v___x_4634_, v_type_4078_, v___x_4593_);
v___x_4636_ = l_Lean_mkApp3(v___x_4626_, v___x_4632_, v_type_4078_, v___x_4635_);
v___x_4637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4638_ = l_Lean_mkConst(v___x_4637_, v___y_4578_);
v___x_4639_ = l_Lean_Expr_app___override(v___x_4638_, v_type_4078_);
v___x_4640_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4639_, v___x_4593_, v___y_4586_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
lean_dec_ref_known(v___x_4640_, 1);
v___x_4641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc(v___y_4578_);
v___x_4642_ = l_Lean_mkConst(v___x_4641_, v___y_4578_);
lean_inc_ref(v_type_4078_);
v___x_4643_ = l_Lean_Expr_app___override(v___x_4642_, v_type_4078_);
lean_inc_ref(v___x_4602_);
v___x_4644_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4643_, v___x_4602_, v___y_4586_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
lean_dec_ref_known(v___x_4644_, 1);
v___x_4645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4578_);
v___x_4647_ = l_Lean_mkConst(v___x_4646_, v___y_4578_);
v___x_4648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15);
lean_inc_ref(v_type_4078_);
v___x_4649_ = l_Lean_mkAppB(v___x_4647_, v_type_4078_, v___x_4648_);
lean_inc_ref(v___x_4606_);
v___x_4650_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4649_, v___x_4606_, v___y_4586_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
lean_dec_ref_known(v___x_4650_, 1);
v___x_4651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc(v___y_4578_);
lean_inc_n(v_val_4097_, 2);
v___x_4653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_val_4097_);
lean_ctor_set(v___x_4653_, 1, v___y_4578_);
lean_inc_ref(v___x_4653_);
v___x_4654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4654_, 0, v_val_4097_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
lean_inc_ref(v___x_4654_);
v___x_4655_ = l_Lean_mkConst(v___x_4652_, v___x_4654_);
lean_inc_ref_n(v_type_4078_, 3);
v___x_4656_ = l_Lean_mkApp3(v___x_4655_, v_type_4078_, v_type_4078_, v_type_4078_);
lean_inc_ref(v___x_4612_);
v___x_4657_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4656_, v___x_4612_, v___y_4586_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
lean_dec_ref_known(v___x_4657_, 1);
v___x_4658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19));
lean_inc_ref(v___x_4654_);
v___x_4660_ = l_Lean_mkConst(v___x_4659_, v___x_4654_);
lean_inc_ref_n(v_type_4078_, 3);
v___x_4661_ = l_Lean_mkApp3(v___x_4660_, v_type_4078_, v_type_4078_, v_type_4078_);
lean_inc_ref(v___x_4618_);
v___x_4662_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4661_, v___x_4618_, v___y_4586_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
lean_dec_ref_known(v___x_4662_, 1);
v___x_4663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc(v___y_4578_);
v___x_4665_ = l_Lean_mkConst(v___x_4664_, v___y_4578_);
lean_inc_ref(v_type_4078_);
v___x_4666_ = l_Lean_Expr_app___override(v___x_4665_, v_type_4078_);
lean_inc_ref(v___x_4621_);
v___x_4667_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4666_, v___x_4621_, v___y_4586_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_dec_ref_known(v___x_4667_, 1);
v___x_4668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4624_);
lean_ctor_set(v___x_4670_, 1, v___x_4653_);
lean_inc_ref(v___x_4670_);
v___x_4671_ = l_Lean_mkConst(v___x_4669_, v___x_4670_);
lean_inc_ref_n(v_type_4078_, 2);
lean_inc_ref(v___x_4671_);
v___x_4672_ = l_Lean_mkApp3(v___x_4671_, v___x_4627_, v_type_4078_, v_type_4078_);
lean_inc_ref(v___x_4631_);
v___x_4673_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4672_, v___x_4631_, v___y_4586_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
lean_dec_ref_known(v___x_4673_, 1);
lean_inc_ref_n(v_type_4078_, 2);
v___x_4674_ = l_Lean_mkApp3(v___x_4671_, v___x_4632_, v_type_4078_, v_type_4078_);
lean_inc_ref(v___x_4636_);
v___x_4675_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4674_, v___x_4636_, v___y_4586_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_dec_ref_known(v___x_4675_, 1);
if (lean_obj_tag(v___y_4579_) == 1)
{
lean_object* v_val_4676_; lean_object* v___x_4677_; 
v_val_4676_ = lean_ctor_get(v___y_4579_, 0);
lean_inc(v_val_4676_);
v___x_4677_ = l_Lean_leCarrierIsSort(v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; uint8_t v___x_4679_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
v___x_4679_ = lean_unbox(v_a_4678_);
lean_dec(v_a_4678_);
if (v___x_4679_ == 0)
{
lean_inc(v_val_4097_);
v___y_4514_ = v___x_4658_;
v___y_4515_ = v___y_4573_;
v___y_4516_ = v___x_4636_;
v___y_4517_ = v___y_4575_;
v___y_4518_ = v___x_4670_;
v___y_4519_ = v___x_4654_;
v___y_4520_ = v___x_4632_;
v___y_4521_ = v___y_4570_;
v___y_4522_ = v___y_4572_;
v___y_4523_ = v___x_4645_;
v___y_4524_ = v___x_4623_;
v___y_4525_ = v___x_4627_;
v___y_4526_ = v___x_4648_;
v___y_4527_ = v___x_4606_;
v___y_4528_ = v___x_4631_;
v___y_4529_ = v___x_4651_;
v___y_4530_ = v___y_4571_;
v___y_4531_ = v___y_4574_;
v___y_4532_ = v___x_4618_;
v___y_4533_ = v___x_4612_;
v___y_4534_ = v___x_4668_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___x_4621_;
v___y_4537_ = v___x_4663_;
v___y_4538_ = v___x_4603_;
v___y_4539_ = v___y_4576_;
v___y_4540_ = v___x_4602_;
v___y_4541_ = v___y_4578_;
v___y_4542_ = v___y_4579_;
v___y_4543_ = v_val_4676_;
v___y_4544_ = v_noNatDivInstQ_x3f_4580_;
v___y_4545_ = v___x_4593_;
v_____do__lift_4546_ = v_val_4097_;
v___y_4547_ = v___y_4581_;
v___y_4548_ = v___y_4582_;
v___y_4549_ = v___y_4583_;
v___y_4550_ = v___y_4584_;
v___y_4551_ = v___y_4585_;
v___y_4552_ = v___y_4586_;
v___y_4553_ = v___y_4587_;
v___y_4554_ = v___y_4588_;
v___y_4555_ = v___y_4589_;
v___y_4556_ = v___y_4590_;
goto v___jp_4513_;
}
else
{
lean_object* v___x_4680_; 
lean_inc(v_val_4097_);
v___x_4680_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_4514_ = v___x_4658_;
v___y_4515_ = v___y_4573_;
v___y_4516_ = v___x_4636_;
v___y_4517_ = v___y_4575_;
v___y_4518_ = v___x_4670_;
v___y_4519_ = v___x_4654_;
v___y_4520_ = v___x_4632_;
v___y_4521_ = v___y_4570_;
v___y_4522_ = v___y_4572_;
v___y_4523_ = v___x_4645_;
v___y_4524_ = v___x_4623_;
v___y_4525_ = v___x_4627_;
v___y_4526_ = v___x_4648_;
v___y_4527_ = v___x_4606_;
v___y_4528_ = v___x_4631_;
v___y_4529_ = v___x_4651_;
v___y_4530_ = v___y_4571_;
v___y_4531_ = v___y_4574_;
v___y_4532_ = v___x_4618_;
v___y_4533_ = v___x_4612_;
v___y_4534_ = v___x_4668_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___x_4621_;
v___y_4537_ = v___x_4663_;
v___y_4538_ = v___x_4603_;
v___y_4539_ = v___y_4576_;
v___y_4540_ = v___x_4602_;
v___y_4541_ = v___y_4578_;
v___y_4542_ = v___y_4579_;
v___y_4543_ = v_val_4676_;
v___y_4544_ = v_noNatDivInstQ_x3f_4580_;
v___y_4545_ = v___x_4593_;
v_____do__lift_4546_ = v___x_4680_;
v___y_4547_ = v___y_4581_;
v___y_4548_ = v___y_4582_;
v___y_4549_ = v___y_4583_;
v___y_4550_ = v___y_4584_;
v___y_4551_ = v___y_4585_;
v___y_4552_ = v___y_4586_;
v___y_4553_ = v___y_4587_;
v___y_4554_ = v___y_4588_;
v___y_4555_ = v___y_4589_;
v___y_4556_ = v___y_4590_;
goto v___jp_4513_;
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_dec_ref_known(v___y_4579_, 1);
lean_dec(v_val_4676_);
lean_dec_ref_known(v___x_4670_, 2);
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4681_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4677_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4677_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
else
{
lean_dec(v___y_4570_);
v___y_4460_ = v___x_4658_;
v___y_4461_ = v___x_4636_;
v___y_4462_ = v___y_4573_;
v___y_4463_ = v___y_4575_;
v___y_4464_ = v___x_4670_;
v___y_4465_ = v___x_4654_;
v___y_4466_ = v___x_4632_;
v___y_4467_ = v___x_4645_;
v___y_4468_ = v___y_4572_;
v___y_4469_ = v___x_4623_;
v___y_4470_ = v___x_4627_;
v___y_4471_ = v___x_4648_;
v___y_4472_ = v___x_4606_;
v___y_4473_ = v___x_4631_;
v___y_4474_ = v___x_4651_;
v___y_4475_ = v___y_4571_;
v___y_4476_ = v___y_4574_;
v___y_4477_ = v___x_4618_;
v___y_4478_ = v___x_4612_;
v___y_4479_ = v___x_4668_;
v___y_4480_ = v___y_4577_;
v___y_4481_ = v___x_4621_;
v___y_4482_ = v___x_4663_;
v___y_4483_ = v___x_4603_;
v___y_4484_ = v___y_4576_;
v___y_4485_ = v___x_4602_;
v___y_4486_ = v___y_4578_;
v___y_4487_ = v___y_4579_;
v___y_4488_ = v_noNatDivInstQ_x3f_4580_;
v___y_4489_ = v___x_4593_;
v___y_4490_ = v___y_4581_;
v___y_4491_ = v___y_4582_;
v___y_4492_ = v___y_4583_;
v___y_4493_ = v___y_4584_;
v___y_4494_ = v___y_4585_;
v___y_4495_ = v___y_4586_;
v___y_4496_ = v___y_4587_;
v___y_4497_ = v___y_4588_;
v___y_4498_ = v___y_4589_;
v___y_4499_ = v___y_4590_;
goto v___jp_4459_;
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref_known(v___x_4670_, 2);
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4689_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4675_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4675_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v___x_4671_);
lean_dec_ref_known(v___x_4670_, 2);
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4697_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4673_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4673_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref_known(v___x_4653_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4705_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4667_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4667_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref_known(v___x_4653_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4713_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4662_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4662_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref_known(v___x_4654_, 2);
lean_dec_ref_known(v___x_4653_, 2);
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4721_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4657_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4657_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4729_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4650_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4650_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4737_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4644_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4644_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_dec_ref(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4593_);
lean_dec(v_noNatDivInstQ_x3f_4580_);
lean_dec(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_type_4078_);
v_a_4745_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4640_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4640_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
v___jp_4753_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13));
v___x_4773_ = lean_box(0);
lean_inc(v_val_4097_);
v___x_4774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4774_, 0, v_val_4097_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
lean_inc_ref(v___x_4774_);
v___x_4775_ = l_Lean_mkConst(v___x_4772_, v___x_4774_);
lean_inc_ref(v_base_4079_);
v___x_4776_ = l_Lean_Expr_app___override(v___x_4775_, v_base_4079_);
v___x_4777_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4776_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v___x_4777_, 1);
if (lean_obj_tag(v_a_4778_) == 1)
{
lean_object* v_val_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_val_4779_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_val_4779_);
lean_dec_ref_known(v_a_4778_, 1);
v___x_4780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__15));
lean_inc_ref(v___x_4774_);
v___x_4781_ = l_Lean_mkConst(v___x_4780_, v___x_4774_);
lean_inc_ref(v_base_4079_);
v___x_4782_ = l_Lean_mkAppB(v___x_4781_, v_base_4079_, v_val_4779_);
v___x_4783_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4782_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
if (lean_obj_tag(v_a_4784_) == 1)
{
lean_object* v_val_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_val_4785_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_val_4785_);
lean_dec_ref_known(v_a_4784_, 1);
v___x_4786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4774_);
v___x_4787_ = l_Lean_mkConst(v___x_4786_, v___x_4774_);
lean_inc_ref(v_natModuleInst_4080_);
lean_inc_ref(v_base_4079_);
v___x_4788_ = l_Lean_mkAppB(v___x_4787_, v_base_4079_, v_natModuleInst_4080_);
v___x_4789_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4788_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v___x_4789_, 1);
if (lean_obj_tag(v_a_4790_) == 1)
{
lean_object* v_val_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4801_; 
v_val_4791_ = lean_ctor_get(v_a_4790_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v_a_4790_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4793_ = v_a_4790_;
v_isShared_4794_ = v_isSharedCheck_4801_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_val_4791_);
lean_dec(v_a_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4801_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__17));
lean_inc_ref(v___x_4774_);
v___x_4796_ = l_Lean_mkConst(v___x_4795_, v___x_4774_);
lean_inc_ref(v_natModuleInst_4080_);
lean_inc_ref(v_base_4079_);
v___x_4797_ = l_Lean_mkApp4(v___x_4796_, v_base_4079_, v_natModuleInst_4080_, v_val_4785_, v_val_4791_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4797_);
v___x_4799_ = v___x_4793_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
v___y_4570_ = v___y_4755_;
v___y_4571_ = v___y_4754_;
v___y_4572_ = v___y_4757_;
v___y_4573_ = v___y_4756_;
v___y_4574_ = v_isLinearInstQ_x3f_4761_;
v___y_4575_ = v___x_4773_;
v___y_4576_ = v___y_4758_;
v___y_4577_ = v___y_4759_;
v___y_4578_ = v___x_4774_;
v___y_4579_ = v___y_4760_;
v_noNatDivInstQ_x3f_4580_ = v___x_4799_;
v___y_4581_ = v___y_4762_;
v___y_4582_ = v___y_4763_;
v___y_4583_ = v___y_4764_;
v___y_4584_ = v___y_4765_;
v___y_4585_ = v___y_4766_;
v___y_4586_ = v___y_4767_;
v___y_4587_ = v___y_4768_;
v___y_4588_ = v___y_4769_;
v___y_4589_ = v___y_4770_;
v___y_4590_ = v___y_4771_;
goto v___jp_4569_;
}
}
}
else
{
lean_object* v___x_4802_; 
lean_dec(v_a_4790_);
lean_dec(v_val_4785_);
v___x_4802_ = lean_box(0);
v___y_4570_ = v___y_4755_;
v___y_4571_ = v___y_4754_;
v___y_4572_ = v___y_4757_;
v___y_4573_ = v___y_4756_;
v___y_4574_ = v_isLinearInstQ_x3f_4761_;
v___y_4575_ = v___x_4773_;
v___y_4576_ = v___y_4758_;
v___y_4577_ = v___y_4759_;
v___y_4578_ = v___x_4774_;
v___y_4579_ = v___y_4760_;
v_noNatDivInstQ_x3f_4580_ = v___x_4802_;
v___y_4581_ = v___y_4762_;
v___y_4582_ = v___y_4763_;
v___y_4583_ = v___y_4764_;
v___y_4584_ = v___y_4765_;
v___y_4585_ = v___y_4766_;
v___y_4586_ = v___y_4767_;
v___y_4587_ = v___y_4768_;
v___y_4588_ = v___y_4769_;
v___y_4589_ = v___y_4770_;
v___y_4590_ = v___y_4771_;
goto v___jp_4569_;
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v_val_4785_);
lean_dec_ref_known(v___x_4774_, 2);
lean_dec(v_isLinearInstQ_x3f_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec(v___y_4755_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4803_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4789_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4789_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v___x_4811_; 
lean_dec(v_a_4784_);
v___x_4811_ = lean_box(0);
v___y_4570_ = v___y_4755_;
v___y_4571_ = v___y_4754_;
v___y_4572_ = v___y_4757_;
v___y_4573_ = v___y_4756_;
v___y_4574_ = v_isLinearInstQ_x3f_4761_;
v___y_4575_ = v___x_4773_;
v___y_4576_ = v___y_4758_;
v___y_4577_ = v___y_4759_;
v___y_4578_ = v___x_4774_;
v___y_4579_ = v___y_4760_;
v_noNatDivInstQ_x3f_4580_ = v___x_4811_;
v___y_4581_ = v___y_4762_;
v___y_4582_ = v___y_4763_;
v___y_4583_ = v___y_4764_;
v___y_4584_ = v___y_4765_;
v___y_4585_ = v___y_4766_;
v___y_4586_ = v___y_4767_;
v___y_4587_ = v___y_4768_;
v___y_4588_ = v___y_4769_;
v___y_4589_ = v___y_4770_;
v___y_4590_ = v___y_4771_;
goto v___jp_4569_;
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec_ref_known(v___x_4774_, 2);
lean_dec(v_isLinearInstQ_x3f_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec(v___y_4755_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4812_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4783_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4783_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
else
{
lean_object* v___x_4820_; 
lean_dec(v_a_4778_);
v___x_4820_ = lean_box(0);
v___y_4570_ = v___y_4755_;
v___y_4571_ = v___y_4754_;
v___y_4572_ = v___y_4757_;
v___y_4573_ = v___y_4756_;
v___y_4574_ = v_isLinearInstQ_x3f_4761_;
v___y_4575_ = v___x_4773_;
v___y_4576_ = v___y_4758_;
v___y_4577_ = v___y_4759_;
v___y_4578_ = v___x_4774_;
v___y_4579_ = v___y_4760_;
v_noNatDivInstQ_x3f_4580_ = v___x_4820_;
v___y_4581_ = v___y_4762_;
v___y_4582_ = v___y_4763_;
v___y_4583_ = v___y_4764_;
v___y_4584_ = v___y_4765_;
v___y_4585_ = v___y_4766_;
v___y_4586_ = v___y_4767_;
v___y_4587_ = v___y_4768_;
v___y_4588_ = v___y_4769_;
v___y_4589_ = v___y_4770_;
v___y_4590_ = v___y_4771_;
goto v___jp_4569_;
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec_ref_known(v___x_4774_, 2);
lean_dec(v_isLinearInstQ_x3f_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec(v___y_4755_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4821_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4777_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4777_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
v___jp_4829_:
{
lean_object* v___x_4851_; 
lean_inc_ref(v_base_4079_);
v___x_4851_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_____do__lift_4840_, v_base_4079_, v___y_4839_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
if (lean_obj_tag(v_a_4852_) == 0)
{
lean_dec_ref(v___y_4838_);
lean_dec_ref(v___y_4837_);
v___y_4754_ = v___y_4831_;
v___y_4755_ = v___y_4830_;
v___y_4756_ = v___y_4833_;
v___y_4757_ = v___y_4832_;
v___y_4758_ = v___y_4834_;
v___y_4759_ = v___y_4835_;
v___y_4760_ = v___y_4836_;
v_isLinearInstQ_x3f_4761_ = v_a_4852_;
v___y_4762_ = v___y_4841_;
v___y_4763_ = v___y_4842_;
v___y_4764_ = v___y_4843_;
v___y_4765_ = v___y_4844_;
v___y_4766_ = v___y_4845_;
v___y_4767_ = v___y_4846_;
v___y_4768_ = v___y_4847_;
v___y_4769_ = v___y_4848_;
v___y_4770_ = v___y_4849_;
v___y_4771_ = v___y_4850_;
goto v___jp_4753_;
}
else
{
lean_object* v_val_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4862_; 
v_val_4853_ = lean_ctor_get(v_a_4852_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_a_4852_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4855_ = v_a_4852_;
v_isShared_4856_ = v_isSharedCheck_4862_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_val_4853_);
lean_dec(v_a_4852_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4862_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4860_; 
v___x_4857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__19));
lean_inc_ref(v_natModuleInst_4080_);
lean_inc_ref(v_base_4079_);
lean_inc(v_val_4097_);
v___x_4858_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4097_, v_base_4079_, v_natModuleInst_4080_, v___x_4857_, v___y_4838_, v_val_4853_, v___y_4837_);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 0, v___x_4858_);
v___x_4860_ = v___x_4855_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
v___y_4754_ = v___y_4831_;
v___y_4755_ = v___y_4830_;
v___y_4756_ = v___y_4833_;
v___y_4757_ = v___y_4832_;
v___y_4758_ = v___y_4834_;
v___y_4759_ = v___y_4835_;
v___y_4760_ = v___y_4836_;
v_isLinearInstQ_x3f_4761_ = v___x_4860_;
v___y_4762_ = v___y_4841_;
v___y_4763_ = v___y_4842_;
v___y_4764_ = v___y_4843_;
v___y_4765_ = v___y_4844_;
v___y_4766_ = v___y_4845_;
v___y_4767_ = v___y_4846_;
v___y_4768_ = v___y_4847_;
v___y_4769_ = v___y_4848_;
v___y_4770_ = v___y_4849_;
v___y_4771_ = v___y_4850_;
goto v___jp_4753_;
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec(v___y_4830_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4863_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4851_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4851_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
v___jp_4871_:
{
if (lean_obj_tag(v___y_4888_) == 0)
{
lean_object* v___x_4891_; 
lean_dec(v___y_4880_);
v___x_4891_ = lean_box(0);
v___y_4754_ = v___y_4872_;
v___y_4755_ = v___y_4881_;
v___y_4756_ = v___y_4873_;
v___y_4757_ = v___y_4883_;
v___y_4758_ = v___y_4884_;
v___y_4759_ = v___y_4890_;
v___y_4760_ = v___y_4887_;
v_isLinearInstQ_x3f_4761_ = v___x_4891_;
v___y_4762_ = v___y_4876_;
v___y_4763_ = v___y_4885_;
v___y_4764_ = v___y_4878_;
v___y_4765_ = v___y_4874_;
v___y_4766_ = v___y_4877_;
v___y_4767_ = v___y_4889_;
v___y_4768_ = v___y_4886_;
v___y_4769_ = v___y_4882_;
v___y_4770_ = v___y_4879_;
v___y_4771_ = v___y_4875_;
goto v___jp_4753_;
}
else
{
lean_object* v_val_4892_; lean_object* v_snd_4893_; lean_object* v_fst_4894_; lean_object* v_snd_4895_; lean_object* v___x_4896_; 
v_val_4892_ = lean_ctor_get(v___y_4888_, 0);
lean_inc(v_val_4892_);
lean_dec_ref_known(v___y_4888_, 1);
v_snd_4893_ = lean_ctor_get(v_val_4892_, 1);
lean_inc(v_snd_4893_);
v_fst_4894_ = lean_ctor_get(v_val_4892_, 0);
lean_inc(v_fst_4894_);
lean_dec(v_val_4892_);
v_snd_4895_ = lean_ctor_get(v_snd_4893_, 1);
lean_inc(v_snd_4895_);
lean_dec(v_snd_4893_);
v___x_4896_ = l_Lean_leCarrierIsSort(v___y_4879_, v___y_4875_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; uint8_t v___x_4898_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4896_, 1);
v___x_4898_ = lean_unbox(v_a_4897_);
lean_dec(v_a_4897_);
if (v___x_4898_ == 0)
{
lean_inc(v_val_4097_);
v___y_4830_ = v___y_4881_;
v___y_4831_ = v___y_4872_;
v___y_4832_ = v___y_4883_;
v___y_4833_ = v___y_4873_;
v___y_4834_ = v___y_4884_;
v___y_4835_ = v___y_4890_;
v___y_4836_ = v___y_4887_;
v___y_4837_ = v_snd_4895_;
v___y_4838_ = v_fst_4894_;
v___y_4839_ = v___y_4880_;
v_____do__lift_4840_ = v_val_4097_;
v___y_4841_ = v___y_4876_;
v___y_4842_ = v___y_4885_;
v___y_4843_ = v___y_4878_;
v___y_4844_ = v___y_4874_;
v___y_4845_ = v___y_4877_;
v___y_4846_ = v___y_4889_;
v___y_4847_ = v___y_4886_;
v___y_4848_ = v___y_4882_;
v___y_4849_ = v___y_4879_;
v___y_4850_ = v___y_4875_;
goto v___jp_4829_;
}
else
{
lean_object* v___x_4899_; 
lean_inc(v_val_4097_);
v___x_4899_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_4830_ = v___y_4881_;
v___y_4831_ = v___y_4872_;
v___y_4832_ = v___y_4883_;
v___y_4833_ = v___y_4873_;
v___y_4834_ = v___y_4884_;
v___y_4835_ = v___y_4890_;
v___y_4836_ = v___y_4887_;
v___y_4837_ = v_snd_4895_;
v___y_4838_ = v_fst_4894_;
v___y_4839_ = v___y_4880_;
v_____do__lift_4840_ = v___x_4899_;
v___y_4841_ = v___y_4876_;
v___y_4842_ = v___y_4885_;
v___y_4843_ = v___y_4878_;
v___y_4844_ = v___y_4874_;
v___y_4845_ = v___y_4877_;
v___y_4846_ = v___y_4889_;
v___y_4847_ = v___y_4886_;
v___y_4848_ = v___y_4882_;
v___y_4849_ = v___y_4879_;
v___y_4850_ = v___y_4875_;
goto v___jp_4829_;
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec(v_snd_4895_);
lean_dec(v_fst_4894_);
lean_dec(v___y_4890_);
lean_dec(v___y_4887_);
lean_dec(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec(v___y_4873_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4900_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4896_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4896_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
v___jp_4908_:
{
if (lean_obj_tag(v___y_4914_) == 0)
{
lean_dec(v_lawfulOrderLTLvl_4917_);
v___y_4872_ = v___y_4910_;
v___y_4873_ = v___y_4912_;
v___y_4874_ = v___y_4921_;
v___y_4875_ = v___y_4927_;
v___y_4876_ = v___y_4918_;
v___y_4877_ = v___y_4922_;
v___y_4878_ = v___y_4920_;
v___y_4879_ = v___y_4926_;
v___y_4880_ = v___y_4916_;
v___y_4881_ = v___y_4909_;
v___y_4882_ = v___y_4925_;
v___y_4883_ = v___y_4911_;
v___y_4884_ = v___y_4913_;
v___y_4885_ = v___y_4919_;
v___y_4886_ = v___y_4924_;
v___y_4887_ = v___y_4914_;
v___y_4888_ = v___y_4915_;
v___y_4889_ = v___y_4923_;
v___y_4890_ = v___y_4914_;
goto v___jp_4871_;
}
else
{
lean_object* v_val_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v_val_4928_ = lean_ctor_get(v___y_4914_, 0);
v___x_4929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__23));
v___x_4930_ = lean_box(0);
v___x_4931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4931_, 0, v_lawfulOrderLTLvl_4917_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
v___x_4932_ = l_Lean_mkConst(v___x_4929_, v___x_4931_);
lean_inc(v_val_4928_);
lean_inc_ref(v_type_4078_);
v___x_4933_ = l_Lean_mkAppB(v___x_4932_, v_type_4078_, v_val_4928_);
v___x_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
v___y_4872_ = v___y_4910_;
v___y_4873_ = v___y_4912_;
v___y_4874_ = v___y_4921_;
v___y_4875_ = v___y_4927_;
v___y_4876_ = v___y_4918_;
v___y_4877_ = v___y_4922_;
v___y_4878_ = v___y_4920_;
v___y_4879_ = v___y_4926_;
v___y_4880_ = v___y_4916_;
v___y_4881_ = v___y_4909_;
v___y_4882_ = v___y_4925_;
v___y_4883_ = v___y_4911_;
v___y_4884_ = v___y_4913_;
v___y_4885_ = v___y_4919_;
v___y_4886_ = v___y_4924_;
v___y_4887_ = v___y_4914_;
v___y_4888_ = v___y_4915_;
v___y_4889_ = v___y_4923_;
v___y_4890_ = v___x_4934_;
goto v___jp_4871_;
}
}
v___jp_4935_:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Lean_leCarrierIsSort(v___y_4943_, v___y_4946_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; uint8_t v___x_4956_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v___x_4956_ = lean_unbox(v_a_4955_);
lean_dec(v_a_4955_);
if (v___x_4956_ == 0)
{
lean_inc(v_val_4097_);
v___y_4909_ = v___y_4941_;
v___y_4910_ = v___y_4936_;
v___y_4911_ = v___y_4953_;
v___y_4912_ = v___y_4937_;
v___y_4913_ = v___y_4944_;
v___y_4914_ = v___y_4950_;
v___y_4915_ = v___y_4951_;
v___y_4916_ = v___y_4940_;
v_lawfulOrderLTLvl_4917_ = v_val_4097_;
v___y_4918_ = v___y_4947_;
v___y_4919_ = v___y_4942_;
v___y_4920_ = v___y_4952_;
v___y_4921_ = v___y_4938_;
v___y_4922_ = v___y_4939_;
v___y_4923_ = v___y_4948_;
v___y_4924_ = v___y_4949_;
v___y_4925_ = v___y_4945_;
v___y_4926_ = v___y_4943_;
v___y_4927_ = v___y_4946_;
goto v___jp_4908_;
}
else
{
lean_object* v___x_4957_; 
lean_inc(v_val_4097_);
v___x_4957_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_4909_ = v___y_4941_;
v___y_4910_ = v___y_4936_;
v___y_4911_ = v___y_4953_;
v___y_4912_ = v___y_4937_;
v___y_4913_ = v___y_4944_;
v___y_4914_ = v___y_4950_;
v___y_4915_ = v___y_4951_;
v___y_4916_ = v___y_4940_;
v_lawfulOrderLTLvl_4917_ = v___x_4957_;
v___y_4918_ = v___y_4947_;
v___y_4919_ = v___y_4942_;
v___y_4920_ = v___y_4952_;
v___y_4921_ = v___y_4938_;
v___y_4922_ = v___y_4939_;
v___y_4923_ = v___y_4948_;
v___y_4924_ = v___y_4949_;
v___y_4925_ = v___y_4945_;
v___y_4926_ = v___y_4943_;
v___y_4927_ = v___y_4946_;
goto v___jp_4908_;
}
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
lean_dec(v___y_4953_);
lean_dec(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec(v___y_4944_);
lean_dec(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec(v___y_4937_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_4958_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4954_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4954_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
v___jp_4966_:
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_box(0);
lean_inc(v___y_4980_);
v___y_4936_ = v___y_4967_;
v___y_4937_ = v___x_4981_;
v___y_4938_ = v___y_4968_;
v___y_4939_ = v___y_4969_;
v___y_4940_ = v___y_4970_;
v___y_4941_ = v___y_4971_;
v___y_4942_ = v___y_4972_;
v___y_4943_ = v___y_4973_;
v___y_4944_ = v___x_4981_;
v___y_4945_ = v___y_4974_;
v___y_4946_ = v___y_4975_;
v___y_4947_ = v___y_4976_;
v___y_4948_ = v___y_4977_;
v___y_4949_ = v___y_4978_;
v___y_4950_ = v___x_4981_;
v___y_4951_ = v___y_4980_;
v___y_4952_ = v___y_4979_;
v___y_4953_ = v___x_4981_;
goto v___jp_4935_;
}
v___jp_4982_:
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_box(0);
v___y_4967_ = v___y_4984_;
v___y_4968_ = v___y_4989_;
v___y_4969_ = v___y_4990_;
v___y_4970_ = v___y_4985_;
v___y_4971_ = v___y_4983_;
v___y_4972_ = v___y_4987_;
v___y_4973_ = v___y_4994_;
v___y_4974_ = v___y_4993_;
v___y_4975_ = v___y_4995_;
v___y_4976_ = v___y_4986_;
v___y_4977_ = v___y_4991_;
v___y_4978_ = v___y_4992_;
v___y_4979_ = v___y_4988_;
v___y_4980_ = v___x_4996_;
goto v___jp_4966_;
}
v___jp_4997_:
{
if (lean_obj_tag(v___y_5000_) == 0)
{
lean_object* v___x_5012_; 
v___x_5012_ = lean_box(0);
v___y_4967_ = v___y_4998_;
v___y_4968_ = v___y_5005_;
v___y_4969_ = v___y_5006_;
v___y_4970_ = v___y_5001_;
v___y_4971_ = v___y_4999_;
v___y_4972_ = v___y_5003_;
v___y_4973_ = v___y_5010_;
v___y_4974_ = v___y_5009_;
v___y_4975_ = v___y_5011_;
v___y_4976_ = v___y_5002_;
v___y_4977_ = v___y_5007_;
v___y_4978_ = v___y_5008_;
v___y_4979_ = v___y_5004_;
v___y_4980_ = v___x_5012_;
goto v___jp_4966_;
}
else
{
lean_dec_ref_known(v___y_5000_, 1);
v___y_4983_ = v___y_4999_;
v___y_4984_ = v___y_4998_;
v___y_4985_ = v___y_5001_;
v___y_4986_ = v___y_5002_;
v___y_4987_ = v___y_5003_;
v___y_4988_ = v___y_5004_;
v___y_4989_ = v___y_5005_;
v___y_4990_ = v___y_5006_;
v___y_4991_ = v___y_5007_;
v___y_4992_ = v___y_5008_;
v___y_4993_ = v___y_5009_;
v___y_4994_ = v___y_5010_;
v___y_4995_ = v___y_5011_;
goto v___jp_4982_;
}
}
v___jp_5013_:
{
lean_object* v___x_5028_; 
lean_inc(v___y_5016_);
lean_inc_ref(v_base_4079_);
v___x_5028_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_____do__lift_5017_, v_base_4079_, v___y_5016_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
if (lean_obj_tag(v___x_5028_) == 0)
{
if (lean_obj_tag(v___y_5016_) == 1)
{
lean_object* v_a_5029_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5028_, 1);
if (lean_obj_tag(v_a_5029_) == 1)
{
lean_object* v_val_5030_; lean_object* v_val_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5085_; 
v_val_5030_ = lean_ctor_get(v___y_5016_, 0);
v_val_5031_ = lean_ctor_get(v_a_5029_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_a_5029_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5033_ = v_a_5029_;
v_isShared_5034_ = v_isSharedCheck_5085_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_val_5031_);
lean_dec(v_a_5029_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5085_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_base_4079_);
lean_inc(v_val_4097_);
v___x_5036_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_5035_, v_val_4097_, v_base_4079_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
v___x_5039_ = lean_box(0);
lean_inc(v_val_4097_);
v___x_5040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5040_, 0, v_val_4097_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = l_Lean_mkConst(v___x_5038_, v___x_5040_);
lean_inc(v_val_5031_);
lean_inc(v_val_5030_);
lean_inc_ref(v_base_4079_);
v___x_5042_ = l_Lean_mkApp4(v___x_5041_, v_base_4079_, v_a_5037_, v_val_5030_, v_val_5031_);
v___x_5043_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5042_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref_known(v___x_5043_, 1);
if (lean_obj_tag(v_a_5044_) == 0)
{
lean_del_object(v___x_5033_);
lean_dec(v_val_5031_);
v___y_4983_ = v___y_5015_;
v___y_4984_ = v___y_5014_;
v___y_4985_ = v___y_5016_;
v___y_4986_ = v___y_5018_;
v___y_4987_ = v___y_5019_;
v___y_4988_ = v___y_5020_;
v___y_4989_ = v___y_5021_;
v___y_4990_ = v___y_5022_;
v___y_4991_ = v___y_5023_;
v___y_4992_ = v___y_5024_;
v___y_4993_ = v___y_5025_;
v___y_4994_ = v___y_5026_;
v___y_4995_ = v___y_5027_;
goto v___jp_4982_;
}
else
{
lean_object* v_val_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5068_; 
v_val_5045_ = lean_ctor_get(v_a_5044_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_a_5044_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5047_ = v_a_5044_;
v_isShared_5048_ = v_isSharedCheck_5068_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_val_5045_);
lean_dec(v_a_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5068_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5052_; 
lean_inc(v_val_5045_);
lean_inc(v_val_5031_);
v___x_5049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5049_, 0, v_val_5031_);
lean_ctor_set(v___x_5049_, 1, v_val_5045_);
lean_inc(v_val_5030_);
v___x_5050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5050_, 0, v_val_5030_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v___x_5050_);
v___x_5052_ = v___x_5047_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5056_; 
v___x_5053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__25));
lean_inc(v_val_5045_);
lean_inc(v_val_5031_);
lean_inc(v_val_5030_);
lean_inc_ref(v_natModuleInst_4080_);
lean_inc_ref(v_base_4079_);
lean_inc(v_val_4097_);
v___x_5054_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4097_, v_base_4079_, v_natModuleInst_4080_, v___x_5053_, v_val_5030_, v_val_5031_, v_val_5045_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 0, v___x_5054_);
v___x_5056_ = v___x_5033_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5054_);
v___x_5056_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__27));
lean_inc_n(v_val_5045_, 2);
lean_inc_n(v_val_5031_, 2);
lean_inc_n(v_val_5030_, 3);
lean_inc_ref_n(v_natModuleInst_4080_, 3);
lean_inc_ref_n(v_base_4079_, 3);
lean_inc_n(v_val_4097_, 3);
v___x_5058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4097_, v_base_4079_, v_natModuleInst_4080_, v___x_5057_, v_val_5030_, v_val_5031_, v_val_5045_);
v___x_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
v___x_5060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__29));
v___x_5061_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4097_, v_base_4079_, v_natModuleInst_4080_, v___x_5060_, v_val_5030_, v_val_5031_, v_val_5045_);
v___x_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
v___x_5063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__31));
v___x_5064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_4097_, v_base_4079_, v_natModuleInst_4080_, v___x_5063_, v_val_5030_, v_val_5031_, v_val_5045_);
v___x_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
v___y_4936_ = v___y_5014_;
v___y_4937_ = v___x_5062_;
v___y_4938_ = v___y_5021_;
v___y_4939_ = v___y_5022_;
v___y_4940_ = v___y_5016_;
v___y_4941_ = v___y_5015_;
v___y_4942_ = v___y_5019_;
v___y_4943_ = v___y_5026_;
v___y_4944_ = v___x_5059_;
v___y_4945_ = v___y_5025_;
v___y_4946_ = v___y_5027_;
v___y_4947_ = v___y_5018_;
v___y_4948_ = v___y_5023_;
v___y_4949_ = v___y_5024_;
v___y_4950_ = v___x_5056_;
v___y_4951_ = v___x_5052_;
v___y_4952_ = v___y_5020_;
v___y_4953_ = v___x_5065_;
goto v___jp_4935_;
}
}
}
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_del_object(v___x_5033_);
lean_dec(v_val_5031_);
lean_dec_ref_known(v___y_5016_, 1);
lean_dec(v___y_5015_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5069_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5043_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5043_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_del_object(v___x_5033_);
lean_dec(v_val_5031_);
lean_dec_ref_known(v___y_5016_, 1);
lean_dec(v___y_5015_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5077_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5036_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5036_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
else
{
v___y_4998_ = v___y_5014_;
v___y_4999_ = v___y_5015_;
v___y_5000_ = v_a_5029_;
v___y_5001_ = v___y_5016_;
v___y_5002_ = v___y_5018_;
v___y_5003_ = v___y_5019_;
v___y_5004_ = v___y_5020_;
v___y_5005_ = v___y_5021_;
v___y_5006_ = v___y_5022_;
v___y_5007_ = v___y_5023_;
v___y_5008_ = v___y_5024_;
v___y_5009_ = v___y_5025_;
v___y_5010_ = v___y_5026_;
v___y_5011_ = v___y_5027_;
goto v___jp_4997_;
}
}
else
{
if (lean_obj_tag(v___y_5016_) == 0)
{
lean_object* v___x_5086_; 
lean_dec_ref_known(v___x_5028_, 1);
v___x_5086_ = lean_box(0);
v___y_4967_ = v___y_5014_;
v___y_4968_ = v___y_5021_;
v___y_4969_ = v___y_5022_;
v___y_4970_ = v___y_5016_;
v___y_4971_ = v___y_5015_;
v___y_4972_ = v___y_5019_;
v___y_4973_ = v___y_5026_;
v___y_4974_ = v___y_5025_;
v___y_4975_ = v___y_5027_;
v___y_4976_ = v___y_5018_;
v___y_4977_ = v___y_5023_;
v___y_4978_ = v___y_5024_;
v___y_4979_ = v___y_5020_;
v___y_4980_ = v___x_5086_;
goto v___jp_4966_;
}
else
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5028_, 1);
v___y_4998_ = v___y_5014_;
v___y_4999_ = v___y_5015_;
v___y_5000_ = v_a_5087_;
v___y_5001_ = v___y_5016_;
v___y_5002_ = v___y_5018_;
v___y_5003_ = v___y_5019_;
v___y_5004_ = v___y_5020_;
v___y_5005_ = v___y_5021_;
v___y_5006_ = v___y_5022_;
v___y_5007_ = v___y_5023_;
v___y_5008_ = v___y_5024_;
v___y_5009_ = v___y_5025_;
v___y_5010_ = v___y_5026_;
v___y_5011_ = v___y_5027_;
goto v___jp_4997_;
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_dec(v___y_5016_);
lean_dec(v___y_5015_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5088_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5028_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5028_);
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
v___jp_5096_:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
v___x_5109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_base_4079_);
v___x_5110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5109_, v_____do__lift_5097_, v_base_4079_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = l_Lean_leCarrierIsSort(v___y_5106_, v___y_5107_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v_a_5113_; uint8_t v___x_5114_; 
v_a_5113_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_a_5113_);
lean_dec_ref_known(v___x_5112_, 1);
v___x_5114_ = lean_unbox(v_a_5113_);
lean_dec(v_a_5113_);
if (v___x_5114_ == 0)
{
lean_inc(v_val_4097_);
v___y_5014_ = v___x_5108_;
v___y_5015_ = v___x_5109_;
v___y_5016_ = v_a_5111_;
v_____do__lift_5017_ = v_val_4097_;
v___y_5018_ = v___y_5098_;
v___y_5019_ = v___y_5099_;
v___y_5020_ = v___y_5100_;
v___y_5021_ = v___y_5101_;
v___y_5022_ = v___y_5102_;
v___y_5023_ = v___y_5103_;
v___y_5024_ = v___y_5104_;
v___y_5025_ = v___y_5105_;
v___y_5026_ = v___y_5106_;
v___y_5027_ = v___y_5107_;
goto v___jp_5013_;
}
else
{
lean_object* v___x_5115_; 
lean_inc(v_val_4097_);
v___x_5115_ = l_Lean_Level_succ___override(v_val_4097_);
v___y_5014_ = v___x_5108_;
v___y_5015_ = v___x_5109_;
v___y_5016_ = v_a_5111_;
v_____do__lift_5017_ = v___x_5115_;
v___y_5018_ = v___y_5098_;
v___y_5019_ = v___y_5099_;
v___y_5020_ = v___y_5100_;
v___y_5021_ = v___y_5101_;
v___y_5022_ = v___y_5102_;
v___y_5023_ = v___y_5103_;
v___y_5024_ = v___y_5104_;
v___y_5025_ = v___y_5105_;
v___y_5026_ = v___y_5106_;
v___y_5027_ = v___y_5107_;
goto v___jp_5013_;
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
lean_dec(v_a_5111_);
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5116_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5112_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5112_);
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
lean_del_object(v___x_4099_);
lean_dec(v_val_4097_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5124_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5110_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5110_);
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
}
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5147_; 
lean_dec(v_a_4093_);
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v___x_5145_ = lean_box(0);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_5145_);
v___x_5147_ = v___x_4095_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5145_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_dec_ref(v_natModuleInst_4080_);
lean_dec_ref(v_base_4079_);
lean_dec_ref(v_type_4078_);
v_a_5150_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_4092_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_4092_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_5158_, lean_object* v_base_5159_, lean_object* v_natModuleInst_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_5158_, v_base_5159_, v_natModuleInst_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_);
lean_dec(v_a_5170_);
lean_dec_ref(v_a_5169_);
lean_dec(v_a_5168_);
lean_dec_ref(v_a_5167_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5162_);
lean_dec(v_a_5161_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v___x_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; 
v___x_5192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_5193_ = lean_unsigned_to_nat(2u);
v___x_5194_ = l_Lean_Expr_isAppOfArity(v_type_5180_, v___x_5192_, v___x_5193_);
if (v___x_5194_ == 0)
{
lean_object* v___x_5195_; 
v___x_5195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
return v___x_5195_;
}
else
{
lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5196_ = l_Lean_Expr_appFn_x21(v_type_5180_);
v___x_5197_ = l_Lean_Expr_appArg_x21(v___x_5196_);
lean_dec_ref(v___x_5196_);
v___x_5198_ = l_Lean_Expr_appArg_x21(v_type_5180_);
v___x_5199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_5180_, v___x_5197_, v___x_5198_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
return v___x_5199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_);
lean_dec(v_a_5210_);
lean_dec_ref(v_a_5209_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec_ref(v_a_5205_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
lean_dec(v_a_5201_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_5213_, lean_object* v_a_5214_, lean_object* v_s_5215_){
_start:
{
lean_object* v_structs_5216_; lean_object* v_typeIdOf_5217_; lean_object* v_exprToStructId_5218_; lean_object* v_exprToStructIdEntries_5219_; lean_object* v_forbiddenNatModules_5220_; lean_object* v_natStructs_5221_; lean_object* v_natTypeIdOf_5222_; lean_object* v_exprToNatStructId_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5231_; 
v_structs_5216_ = lean_ctor_get(v_s_5215_, 0);
v_typeIdOf_5217_ = lean_ctor_get(v_s_5215_, 1);
v_exprToStructId_5218_ = lean_ctor_get(v_s_5215_, 2);
v_exprToStructIdEntries_5219_ = lean_ctor_get(v_s_5215_, 3);
v_forbiddenNatModules_5220_ = lean_ctor_get(v_s_5215_, 4);
v_natStructs_5221_ = lean_ctor_get(v_s_5215_, 5);
v_natTypeIdOf_5222_ = lean_ctor_get(v_s_5215_, 6);
v_exprToNatStructId_5223_ = lean_ctor_get(v_s_5215_, 7);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_s_5215_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5225_ = v_s_5215_;
v_isShared_5226_ = v_isSharedCheck_5231_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_exprToNatStructId_5223_);
lean_inc(v_natTypeIdOf_5222_);
lean_inc(v_natStructs_5221_);
lean_inc(v_forbiddenNatModules_5220_);
lean_inc(v_exprToStructIdEntries_5219_);
lean_inc(v_exprToStructId_5218_);
lean_inc(v_typeIdOf_5217_);
lean_inc(v_structs_5216_);
lean_dec(v_s_5215_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5231_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v___x_5227_; lean_object* v___x_5229_; 
v___x_5227_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_5217_, v_type_5213_, v_a_5214_);
if (v_isShared_5226_ == 0)
{
lean_ctor_set(v___x_5225_, 1, v___x_5227_);
v___x_5229_ = v___x_5225_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_structs_5216_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v___x_5227_);
lean_ctor_set(v_reuseFailAlloc_5230_, 2, v_exprToStructId_5218_);
lean_ctor_set(v_reuseFailAlloc_5230_, 3, v_exprToStructIdEntries_5219_);
lean_ctor_set(v_reuseFailAlloc_5230_, 4, v_forbiddenNatModules_5220_);
lean_ctor_set(v_reuseFailAlloc_5230_, 5, v_natStructs_5221_);
lean_ctor_set(v_reuseFailAlloc_5230_, 6, v_natTypeIdOf_5222_);
lean_ctor_set(v_reuseFailAlloc_5230_, 7, v_exprToNatStructId_5223_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5232_, lean_object* v_vals_5233_, lean_object* v_i_5234_, lean_object* v_k_5235_){
_start:
{
lean_object* v___x_5236_; uint8_t v___x_5237_; 
v___x_5236_ = lean_array_get_size(v_keys_5232_);
v___x_5237_ = lean_nat_dec_lt(v_i_5234_, v___x_5236_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; 
lean_dec(v_i_5234_);
v___x_5238_ = lean_box(0);
return v___x_5238_;
}
else
{
lean_object* v_k_x27_5239_; size_t v___x_5240_; size_t v___x_5241_; uint8_t v___x_5242_; 
v_k_x27_5239_ = lean_array_fget_borrowed(v_keys_5232_, v_i_5234_);
v___x_5240_ = lean_ptr_addr(v_k_5235_);
v___x_5241_ = lean_ptr_addr(v_k_x27_5239_);
v___x_5242_ = lean_usize_dec_eq(v___x_5240_, v___x_5241_);
if (v___x_5242_ == 0)
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5243_ = lean_unsigned_to_nat(1u);
v___x_5244_ = lean_nat_add(v_i_5234_, v___x_5243_);
lean_dec(v_i_5234_);
v_i_5234_ = v___x_5244_;
goto _start;
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5246_ = lean_array_fget_borrowed(v_vals_5233_, v_i_5234_);
lean_dec(v_i_5234_);
lean_inc(v___x_5246_);
v___x_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5246_);
return v___x_5247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5248_, lean_object* v_vals_5249_, lean_object* v_i_5250_, lean_object* v_k_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5248_, v_vals_5249_, v_i_5250_, v_k_5251_);
lean_dec_ref(v_k_5251_);
lean_dec_ref(v_vals_5249_);
lean_dec_ref(v_keys_5248_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5253_, size_t v_x_5254_, lean_object* v_x_5255_){
_start:
{
if (lean_obj_tag(v_x_5253_) == 0)
{
lean_object* v_es_5256_; lean_object* v___x_5257_; size_t v___x_5258_; size_t v___x_5259_; lean_object* v_j_5260_; lean_object* v___x_5261_; 
v_es_5256_ = lean_ctor_get(v_x_5253_, 0);
v___x_5257_ = lean_box(2);
v___x_5258_ = ((size_t)31ULL);
v___x_5259_ = lean_usize_land(v_x_5254_, v___x_5258_);
v_j_5260_ = lean_usize_to_nat(v___x_5259_);
v___x_5261_ = lean_array_get_borrowed(v___x_5257_, v_es_5256_, v_j_5260_);
lean_dec(v_j_5260_);
switch(lean_obj_tag(v___x_5261_))
{
case 0:
{
lean_object* v_key_5262_; lean_object* v_val_5263_; size_t v___x_5264_; size_t v___x_5265_; uint8_t v___x_5266_; 
v_key_5262_ = lean_ctor_get(v___x_5261_, 0);
v_val_5263_ = lean_ctor_get(v___x_5261_, 1);
v___x_5264_ = lean_ptr_addr(v_x_5255_);
v___x_5265_ = lean_ptr_addr(v_key_5262_);
v___x_5266_ = lean_usize_dec_eq(v___x_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; 
v___x_5267_ = lean_box(0);
return v___x_5267_;
}
else
{
lean_object* v___x_5268_; 
lean_inc(v_val_5263_);
v___x_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5268_, 0, v_val_5263_);
return v___x_5268_;
}
}
case 1:
{
lean_object* v_node_5269_; size_t v___x_5270_; size_t v___x_5271_; 
v_node_5269_ = lean_ctor_get(v___x_5261_, 0);
v___x_5270_ = ((size_t)5ULL);
v___x_5271_ = lean_usize_shift_right(v_x_5254_, v___x_5270_);
v_x_5253_ = v_node_5269_;
v_x_5254_ = v___x_5271_;
goto _start;
}
default: 
{
lean_object* v___x_5273_; 
v___x_5273_ = lean_box(0);
return v___x_5273_;
}
}
}
else
{
lean_object* v_ks_5274_; lean_object* v_vs_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v_ks_5274_ = lean_ctor_get(v_x_5253_, 0);
v_vs_5275_ = lean_ctor_get(v_x_5253_, 1);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5274_, v_vs_5275_, v___x_5276_, v_x_5255_);
return v___x_5277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5278_, lean_object* v_x_5279_, lean_object* v_x_5280_){
_start:
{
size_t v_x_6741__boxed_5281_; lean_object* v_res_5282_; 
v_x_6741__boxed_5281_ = lean_unbox_usize(v_x_5279_);
lean_dec(v_x_5279_);
v_res_5282_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5278_, v_x_6741__boxed_5281_, v_x_5280_);
lean_dec_ref(v_x_5280_);
lean_dec_ref(v_x_5278_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_5283_, lean_object* v_x_5284_){
_start:
{
size_t v___x_5285_; size_t v___x_5286_; size_t v___x_5287_; uint64_t v___x_5288_; size_t v___x_5289_; lean_object* v___x_5290_; 
v___x_5285_ = lean_ptr_addr(v_x_5284_);
v___x_5286_ = ((size_t)3ULL);
v___x_5287_ = lean_usize_shift_right(v___x_5285_, v___x_5286_);
v___x_5288_ = lean_usize_to_uint64(v___x_5287_);
v___x_5289_ = lean_uint64_to_usize(v___x_5288_);
v___x_5290_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5283_, v___x_5289_, v_x_5284_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5291_, lean_object* v_x_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_5291_, v_x_5292_);
lean_dec_ref(v_x_5292_);
lean_dec_ref(v_x_5291_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5297_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5376_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5309_ = v___x_5306_;
v_isShared_5310_ = v_isSharedCheck_5376_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5306_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5376_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
uint8_t v_linarith_5311_; 
v_linarith_5311_ = lean_ctor_get_uint8(v_a_5307_, sizeof(void*)*18 + 23);
lean_dec(v_a_5307_);
if (v_linarith_5311_ == 0)
{
lean_object* v___x_5312_; lean_object* v___x_5314_; 
lean_dec_ref(v_type_5294_);
v___x_5312_ = lean_box(0);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5312_);
v___x_5314_ = v___x_5309_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5312_);
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
lean_del_object(v___x_5309_);
lean_inc_ref(v_type_5294_);
v___x_5316_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_type_5294_, v_a_5297_, v_a_5302_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5367_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5319_ = v___x_5316_;
v_isShared_5320_ = v_isSharedCheck_5367_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5367_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
uint8_t v___x_5321_; 
v___x_5321_ = lean_unbox(v_a_5317_);
lean_dec(v_a_5317_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; 
lean_del_object(v___x_5319_);
v___x_5322_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5295_, v_a_5303_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5354_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5325_ = v___x_5322_;
v_isShared_5326_ = v_isSharedCheck_5354_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5322_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5354_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v_typeIdOf_5327_; lean_object* v___x_5328_; 
v_typeIdOf_5327_ = lean_ctor_get(v_a_5323_, 1);
lean_inc_ref(v_typeIdOf_5327_);
lean_dec(v_a_5323_);
v___x_5328_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_5327_, v_type_5294_);
lean_dec_ref(v_typeIdOf_5327_);
if (lean_obj_tag(v___x_5328_) == 1)
{
lean_object* v_val_5329_; lean_object* v___x_5331_; 
lean_dec_ref(v_type_5294_);
v_val_5329_ = lean_ctor_get(v___x_5328_, 0);
lean_inc(v_val_5329_);
lean_dec_ref_known(v___x_5328_, 1);
if (v_isShared_5326_ == 0)
{
lean_ctor_set(v___x_5325_, 0, v_val_5329_);
v___x_5331_ = v___x_5325_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_val_5329_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
else
{
lean_object* v___x_5333_; 
lean_dec(v___x_5328_);
lean_del_object(v___x_5325_);
lean_inc_ref(v_type_5294_);
v___x_5333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_);
if (lean_obj_tag(v___x_5333_) == 0)
{
lean_object* v_a_5334_; lean_object* v___f_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; 
v_a_5334_ = lean_ctor_get(v___x_5333_, 0);
lean_inc_n(v_a_5334_, 2);
lean_dec_ref_known(v___x_5333_, 1);
v___f_5335_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5335_, 0, v_type_5294_);
lean_closure_set(v___f_5335_, 1, v_a_5334_);
v___x_5336_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5337_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5336_, v___f_5335_, v_a_5295_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5344_ == 0)
{
lean_object* v_unused_5345_; 
v_unused_5345_ = lean_ctor_get(v___x_5337_, 0);
lean_dec(v_unused_5345_);
v___x_5339_ = v___x_5337_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_dec(v___x_5337_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v_a_5334_);
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5334_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec(v_a_5334_);
v_a_5346_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5337_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5337_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
else
{
lean_dec_ref(v_type_5294_);
return v___x_5333_;
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
lean_dec_ref(v_type_5294_);
v_a_5355_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5322_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5322_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
else
{
lean_object* v___x_5363_; lean_object* v___x_5365_; 
lean_dec_ref(v_type_5294_);
v___x_5363_ = lean_box(0);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5363_);
v___x_5365_ = v___x_5319_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec_ref(v_type_5294_);
v_a_5368_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5316_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5316_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
lean_dec_ref(v_type_5294_);
v_a_5377_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5306_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5306_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec_ref(v_a_5392_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec(v_a_5386_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_5398_, lean_object* v_x_5399_, lean_object* v_x_5400_){
_start:
{
lean_object* v___x_5401_; 
v___x_5401_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_5399_, v_x_5400_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5402_, lean_object* v_x_5403_, lean_object* v_x_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_5402_, v_x_5403_, v_x_5404_);
lean_dec_ref(v_x_5404_);
lean_dec_ref(v_x_5403_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5406_, lean_object* v_x_5407_, size_t v_x_5408_, lean_object* v_x_5409_){
_start:
{
lean_object* v___x_5410_; 
v___x_5410_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_5407_, v_x_5408_, v_x_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5411_, lean_object* v_x_5412_, lean_object* v_x_5413_, lean_object* v_x_5414_){
_start:
{
size_t v_x_6977__boxed_5415_; lean_object* v_res_5416_; 
v_x_6977__boxed_5415_ = lean_unbox_usize(v_x_5413_);
lean_dec(v_x_5413_);
v_res_5416_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_5411_, v_x_5412_, v_x_6977__boxed_5415_, v_x_5414_);
lean_dec_ref(v_x_5414_);
lean_dec_ref(v_x_5412_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5417_, lean_object* v_keys_5418_, lean_object* v_vals_5419_, lean_object* v_heq_5420_, lean_object* v_i_5421_, lean_object* v_k_5422_){
_start:
{
lean_object* v___x_5423_; 
v___x_5423_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5418_, v_vals_5419_, v_i_5421_, v_k_5422_);
return v___x_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5424_, lean_object* v_keys_5425_, lean_object* v_vals_5426_, lean_object* v_heq_5427_, lean_object* v_i_5428_, lean_object* v_k_5429_){
_start:
{
lean_object* v_res_5430_; 
v_res_5430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5424_, v_keys_5425_, v_vals_5426_, v_heq_5427_, v_i_5428_, v_k_5429_);
lean_dec_ref(v_k_5429_);
lean_dec_ref(v_vals_5426_);
lean_dec_ref(v_keys_5425_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_5431_, lean_object* v_type_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_5440_ = lean_box(0);
v___x_5441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5441_, 0, v_u_5431_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
v___x_5442_ = l_Lean_mkConst(v___x_5439_, v___x_5441_);
v___x_5443_ = l_Lean_Expr_app___override(v___x_5442_, v_type_5432_);
v___x_5444_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5443_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_5445_, lean_object* v_type_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_5445_, v_type_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_);
lean_dec(v_a_5451_);
lean_dec_ref(v_a_5450_);
lean_dec(v_a_5449_);
lean_dec_ref(v_a_5448_);
lean_dec(v_a_5447_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_5454_, lean_object* v_type_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_){
_start:
{
lean_object* v___x_5467_; 
v___x_5467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_5454_, v_type_5455_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_5468_, lean_object* v_type_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_5468_, v_type_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_);
lean_dec(v_a_5479_);
lean_dec_ref(v_a_5478_);
lean_dec(v_a_5477_);
lean_dec_ref(v_a_5476_);
lean_dec(v_a_5475_);
lean_dec_ref(v_a_5474_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
lean_dec(v_a_5471_);
lean_dec(v_a_5470_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_5482_, lean_object* v_s_5483_){
_start:
{
lean_object* v_structs_5484_; lean_object* v_typeIdOf_5485_; lean_object* v_exprToStructId_5486_; lean_object* v_exprToStructIdEntries_5487_; lean_object* v_forbiddenNatModules_5488_; lean_object* v_natStructs_5489_; lean_object* v_natTypeIdOf_5490_; lean_object* v_exprToNatStructId_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5499_; 
v_structs_5484_ = lean_ctor_get(v_s_5483_, 0);
v_typeIdOf_5485_ = lean_ctor_get(v_s_5483_, 1);
v_exprToStructId_5486_ = lean_ctor_get(v_s_5483_, 2);
v_exprToStructIdEntries_5487_ = lean_ctor_get(v_s_5483_, 3);
v_forbiddenNatModules_5488_ = lean_ctor_get(v_s_5483_, 4);
v_natStructs_5489_ = lean_ctor_get(v_s_5483_, 5);
v_natTypeIdOf_5490_ = lean_ctor_get(v_s_5483_, 6);
v_exprToNatStructId_5491_ = lean_ctor_get(v_s_5483_, 7);
v_isSharedCheck_5499_ = !lean_is_exclusive(v_s_5483_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5493_ = v_s_5483_;
v_isShared_5494_ = v_isSharedCheck_5499_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_exprToNatStructId_5491_);
lean_inc(v_natTypeIdOf_5490_);
lean_inc(v_natStructs_5489_);
lean_inc(v_forbiddenNatModules_5488_);
lean_inc(v_exprToStructIdEntries_5487_);
lean_inc(v_exprToStructId_5486_);
lean_inc(v_typeIdOf_5485_);
lean_inc(v_structs_5484_);
lean_dec(v_s_5483_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5499_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5495_; lean_object* v___x_5497_; 
v___x_5495_ = lean_array_push(v_natStructs_5489_, v___x_5482_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 5, v___x_5495_);
v___x_5497_ = v___x_5493_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_structs_5484_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v_typeIdOf_5485_);
lean_ctor_set(v_reuseFailAlloc_5498_, 2, v_exprToStructId_5486_);
lean_ctor_set(v_reuseFailAlloc_5498_, 3, v_exprToStructIdEntries_5487_);
lean_ctor_set(v_reuseFailAlloc_5498_, 4, v_forbiddenNatModules_5488_);
lean_ctor_set(v_reuseFailAlloc_5498_, 5, v___x_5495_);
lean_ctor_set(v_reuseFailAlloc_5498_, 6, v_natTypeIdOf_5490_);
lean_ctor_set(v_reuseFailAlloc_5498_, 7, v_exprToNatStructId_5491_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_){
_start:
{
lean_object* v_ref_5506_; lean_object* v___x_5507_; lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5516_; 
v_ref_5506_ = lean_ctor_get(v___y_5503_, 2);
v___x_5507_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_);
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5510_ = v___x_5507_;
v_isShared_5511_ = v_isSharedCheck_5516_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5507_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5516_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5512_; lean_object* v___x_5514_; 
lean_inc(v_ref_5506_);
v___x_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5512_, 0, v_ref_5506_);
lean_ctor_set(v___x_5512_, 1, v_a_5508_);
if (v_isShared_5511_ == 0)
{
lean_ctor_set_tag(v___x_5510_, 1);
lean_ctor_set(v___x_5510_, 0, v___x_5512_);
v___x_5514_ = v___x_5510_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5512_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
return v_res_5523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4(void){
_start:
{
lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1);
v___x_5531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5530_);
return v___x_5531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6(void){
_start:
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5));
v___x_5534_ = l_Lean_stringToMessageData(v___x_5533_);
return v___x_5534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_){
_start:
{
lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v_orderedAddInst_x3f_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; lean_object* v___y_5573_; lean_object* v___y_5574_; lean_object* v___y_5575_; lean_object* v___y_5707_; lean_object* v___y_5708_; lean_object* v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v___y_5722_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; lean_object* v___y_5742_; lean_object* v___y_5743_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v_____do__lift_5750_; lean_object* v___y_5751_; lean_object* v___y_5752_; lean_object* v___y_5753_; lean_object* v___y_5754_; lean_object* v___y_5755_; lean_object* v___y_5756_; lean_object* v___y_5757_; lean_object* v___y_5758_; lean_object* v___y_5759_; lean_object* v___y_5760_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v_____do__lift_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5833_; lean_object* v___y_5834_; lean_object* v___y_5835_; lean_object* v___y_5836_; lean_object* v___y_5837_; lean_object* v___y_5838_; lean_object* v___y_5839_; lean_object* v___y_5863_; lean_object* v___y_5864_; lean_object* v___y_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; lean_object* v_____do__lift_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___y_5880_; lean_object* v___y_5881_; lean_object* v___y_5882_; lean_object* v___y_5883_; lean_object* v___y_5884_; lean_object* v___y_5885_; lean_object* v___y_5909_; lean_object* v___y_5910_; lean_object* v___y_5911_; lean_object* v___y_5912_; lean_object* v___y_5913_; lean_object* v___y_5914_; lean_object* v___y_5915_; lean_object* v___y_5916_; lean_object* v___y_5917_; lean_object* v___y_5918_; lean_object* v___y_5919_; lean_object* v_____do__lift_5920_; lean_object* v___y_5921_; lean_object* v___y_5922_; lean_object* v___y_5923_; lean_object* v___y_5924_; lean_object* v___y_5925_; lean_object* v___y_5926_; lean_object* v___y_5927_; lean_object* v___y_5928_; lean_object* v___y_5929_; lean_object* v___y_5930_; lean_object* v___y_5955_; lean_object* v___y_5956_; lean_object* v___y_5957_; lean_object* v___y_5958_; lean_object* v___y_5959_; lean_object* v___y_5960_; lean_object* v___y_5961_; lean_object* v___y_5962_; lean_object* v___y_5963_; lean_object* v___y_5964_; lean_object* v_____do__lift_5965_; lean_object* v___y_5966_; lean_object* v___y_5967_; lean_object* v___y_5968_; lean_object* v___y_5969_; lean_object* v___y_5970_; lean_object* v___y_5971_; lean_object* v___y_5972_; lean_object* v___y_5973_; lean_object* v___y_5974_; lean_object* v___y_5975_; lean_object* v_val_6000_; lean_object* v___x_6068_; 
v___x_6068_ = l_Lean_leCarrierIsSort(v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6068_) == 0)
{
lean_object* v_a_6069_; uint8_t v___x_6070_; 
v_a_6069_ = lean_ctor_get(v___x_6068_, 0);
lean_inc(v_a_6069_);
lean_dec_ref_known(v___x_6068_, 1);
v___x_6070_ = lean_unbox(v_a_6069_);
lean_dec(v_a_6069_);
if (v___x_6070_ == 0)
{
lean_object* v___x_6071_; 
lean_inc_ref(v_type_5535_);
v___x_6071_ = l_Lean_Meta_getDecLevel(v_type_5535_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_object* v_a_6072_; 
v_a_6072_ = lean_ctor_get(v___x_6071_, 0);
lean_inc(v_a_6072_);
lean_dec_ref_known(v___x_6071_, 1);
v_val_6000_ = v_a_6072_;
goto v___jp_5999_;
}
else
{
lean_object* v_a_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6080_; 
lean_dec_ref(v_type_5535_);
v_a_6073_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6080_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6080_ == 0)
{
v___x_6075_ = v___x_6071_;
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
else
{
lean_inc(v_a_6073_);
lean_dec(v___x_6071_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
lean_object* v___x_6078_; 
if (v_isShared_6076_ == 0)
{
v___x_6078_ = v___x_6075_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_a_6073_);
v___x_6078_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
return v___x_6078_;
}
}
}
}
else
{
lean_object* v___x_6081_; 
lean_inc_ref(v_type_5535_);
v___x_6081_ = l_Lean_Meta_getDecLevel_x3f(v_type_5535_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6081_) == 0)
{
lean_object* v_a_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6091_; 
v_a_6082_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6084_ = v___x_6081_;
v_isShared_6085_ = v_isSharedCheck_6091_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_a_6082_);
lean_dec(v___x_6081_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6091_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
if (lean_obj_tag(v_a_6082_) == 1)
{
lean_object* v_val_6086_; 
lean_del_object(v___x_6084_);
v_val_6086_ = lean_ctor_get(v_a_6082_, 0);
lean_inc(v_val_6086_);
lean_dec_ref_known(v_a_6082_, 1);
v_val_6000_ = v_val_6086_;
goto v___jp_5999_;
}
else
{
lean_object* v___x_6087_; lean_object* v___x_6089_; 
lean_dec(v_a_6082_);
lean_dec_ref(v_type_5535_);
v___x_6087_ = lean_box(0);
if (v_isShared_6085_ == 0)
{
lean_ctor_set(v___x_6084_, 0, v___x_6087_);
v___x_6089_ = v___x_6084_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v___x_6087_);
v___x_6089_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
return v___x_6089_;
}
}
}
}
else
{
lean_object* v_a_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6099_; 
lean_dec_ref(v_type_5535_);
v_a_6092_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6094_ = v___x_6081_;
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_a_6092_);
lean_dec(v___x_6081_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6097_; 
if (v_isShared_6095_ == 0)
{
v___x_6097_ = v___x_6094_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
v___x_6097_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
return v___x_6097_;
}
}
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_dec_ref(v_type_5535_);
v_a_6100_ = lean_ctor_get(v___x_6068_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_6068_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_6068_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6068_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6105_; 
if (v_isShared_6103_ == 0)
{
v___x_6105_ = v___x_6102_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
v___x_6105_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
return v___x_6105_;
}
}
}
v___jp_5547_:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__13));
lean_inc(v___y_5559_);
v___x_5577_ = l_Lean_mkConst(v___x_5576_, v___y_5559_);
lean_inc_ref(v_type_5535_);
v___x_5578_ = l_Lean_Expr_app___override(v___x_5577_, v_type_5535_);
v___x_5579_ = l_Lean_Meta_Sym_synthInstance(v___x_5578_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5580_);
lean_dec_ref_known(v___x_5579_, 1);
v___x_5581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___y_5548_);
lean_inc_ref(v___y_5563_);
v___x_5582_ = l_Lean_Name_mkStr3(v___y_5563_, v___y_5548_, v___x_5581_);
lean_inc(v___y_5559_);
v___x_5583_ = l_Lean_mkConst(v___x_5582_, v___y_5559_);
lean_inc_ref(v_type_5535_);
v___x_5584_ = l_Lean_mkAppB(v___x_5583_, v_type_5535_, v_a_5580_);
v___x_5585_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5584_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v_a_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
lean_inc(v_a_5586_);
lean_dec_ref_known(v___x_5585_, 1);
v___x_5587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__0));
lean_inc_ref(v___y_5555_);
lean_inc_ref(v___y_5562_);
lean_inc_ref(v___y_5548_);
lean_inc_ref(v___y_5563_);
v___x_5588_ = l_Lean_Name_mkStr5(v___y_5563_, v___y_5548_, v___y_5562_, v___y_5555_, v___x_5587_);
lean_inc(v___y_5559_);
v___x_5589_ = l_Lean_mkConst(v___x_5588_, v___y_5559_);
lean_inc_ref(v___y_5552_);
lean_inc_ref(v_type_5535_);
v___x_5590_ = l_Lean_mkAppB(v___x_5589_, v_type_5535_, v___y_5552_);
v___x_5591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5590_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_a_5592_);
lean_dec_ref_known(v___x_5591_, 1);
v___x_5593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
lean_inc_ref(v_type_5535_);
lean_inc(v___y_5557_);
v___x_5594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_5593_, v___y_5557_, v_type_5535_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___x_5594_, 1);
v___x_5596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_5597_ = l_Lean_mkConst(v___x_5596_, v___y_5559_);
lean_inc_ref(v_type_5535_);
v___x_5598_ = l_Lean_mkAppB(v___x_5597_, v_type_5535_, v_a_5595_);
v___x_5599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_5598_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_a_5600_; lean_object* v___x_5601_; 
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
lean_inc(v_a_5600_);
lean_dec_ref_known(v___x_5599_, 1);
lean_inc_ref(v_type_5535_);
lean_inc(v___y_5557_);
v___x_5601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v___y_5557_, v_type_5535_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_a_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
lean_inc(v_a_5602_);
lean_dec_ref_known(v___x_5601_, 1);
v___x_5603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_5604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_5605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
lean_ctor_set(v___x_5605_, 1, v___y_5564_);
v___x_5606_ = l_Lean_mkConst(v___x_5603_, v___x_5605_);
v___x_5607_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_5535_, 2);
v___x_5608_ = l_Lean_mkApp4(v___x_5606_, v___x_5607_, v_type_5535_, v_type_5535_, v_a_5602_);
v___x_5609_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5608_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v_a_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
lean_inc(v_a_5610_);
lean_dec_ref_known(v___x_5609_, 1);
v___x_5611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__3));
lean_inc(v___y_5557_);
v___x_5612_ = l_Lean_Level_succ___override(v___y_5557_);
lean_inc(v___y_5558_);
v___x_5613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5612_);
lean_ctor_set(v___x_5613_, 1, v___y_5558_);
v___x_5614_ = l_Lean_mkConst(v___x_5611_, v___x_5613_);
v___x_5615_ = l_Lean_Expr_app___override(v___x_5614_, v___y_5556_);
v___x_5616_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_5566_, v___y_5574_);
if (lean_obj_tag(v___x_5616_) == 0)
{
lean_object* v_a_5617_; lean_object* v_natStructs_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___f_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
lean_inc(v_a_5617_);
lean_dec_ref_known(v___x_5616_, 1);
v_natStructs_5618_ = lean_ctor_get(v_a_5617_, 5);
lean_inc_ref(v_natStructs_5618_);
lean_dec(v_a_5617_);
v___x_5619_ = lean_array_get_size(v_natStructs_5618_);
lean_dec_ref(v_natStructs_5618_);
v___x_5620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4);
v___x_5621_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5619_);
lean_ctor_set(v___x_5621_, 1, v___y_5549_);
lean_ctor_set(v___x_5621_, 2, v_type_5535_);
lean_ctor_set(v___x_5621_, 3, v___y_5557_);
lean_ctor_set(v___x_5621_, 4, v___y_5552_);
lean_ctor_set(v___x_5621_, 5, v___y_5553_);
lean_ctor_set(v___x_5621_, 6, v___y_5554_);
lean_ctor_set(v___x_5621_, 7, v___y_5551_);
lean_ctor_set(v___x_5621_, 8, v___y_5550_);
lean_ctor_set(v___x_5621_, 9, v_orderedAddInst_x3f_5565_);
lean_ctor_set(v___x_5621_, 10, v___y_5561_);
lean_ctor_set(v___x_5621_, 11, v_a_5586_);
lean_ctor_set(v___x_5621_, 12, v___x_5615_);
lean_ctor_set(v___x_5621_, 13, v_a_5600_);
lean_ctor_set(v___x_5621_, 14, v_a_5592_);
lean_ctor_set(v___x_5621_, 15, v___y_5560_);
lean_ctor_set(v___x_5621_, 16, v_a_5610_);
lean_ctor_set(v___x_5621_, 17, v___x_5620_);
v___f_5622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_5622_, 0, v___x_5621_);
v___x_5623_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5624_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5623_, v___f_5622_, v___y_5566_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5632_; 
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; 
v_unused_5633_ = lean_ctor_get(v___x_5624_, 0);
lean_dec(v_unused_5633_);
v___x_5626_ = v___x_5624_;
v_isShared_5627_ = v_isSharedCheck_5632_;
goto v_resetjp_5625_;
}
else
{
lean_dec(v___x_5624_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5632_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5628_; lean_object* v___x_5630_; 
v___x_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5628_, 0, v___x_5619_);
if (v_isShared_5627_ == 0)
{
lean_ctor_set(v___x_5626_, 0, v___x_5628_);
v___x_5630_ = v___x_5626_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5628_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
v_a_5634_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5636_ = v___x_5624_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5624_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
lean_dec_ref(v___x_5615_);
lean_dec(v_a_5610_);
lean_dec(v_a_5600_);
lean_dec(v_a_5592_);
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5557_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5642_ = lean_ctor_get(v___x_5616_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5616_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5616_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5616_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
else
{
lean_object* v_a_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5657_; 
lean_dec(v_a_5600_);
lean_dec(v_a_5592_);
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5650_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5652_ = v___x_5609_;
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_a_5650_);
lean_dec(v___x_5609_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5655_; 
if (v_isShared_5653_ == 0)
{
v___x_5655_ = v___x_5652_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v_a_5600_);
lean_dec(v_a_5592_);
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5658_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5601_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5601_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec(v_a_5592_);
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5666_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5599_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5599_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec(v_a_5592_);
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5674_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5594_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5594_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
else
{
lean_object* v_a_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5689_; 
lean_dec(v_a_5586_);
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5682_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5684_ = v___x_5591_;
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_a_5682_);
lean_dec(v___x_5591_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v___x_5687_; 
if (v_isShared_5685_ == 0)
{
v___x_5687_ = v___x_5684_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_a_5682_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5690_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5585_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5585_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
else
{
lean_object* v_a_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5705_; 
lean_dec(v_orderedAddInst_x3f_5565_);
lean_dec(v___y_5564_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v_type_5535_);
v_a_5698_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5700_ = v___x_5579_;
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_a_5698_);
lean_dec(v___x_5579_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5703_; 
if (v_isShared_5701_ == 0)
{
v___x_5703_ = v___x_5700_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
}
v___jp_5706_:
{
lean_object* v___x_5734_; 
v___x_5734_ = lean_box(0);
v___y_5548_ = v___y_5707_;
v___y_5549_ = v___y_5708_;
v___y_5550_ = v___y_5709_;
v___y_5551_ = v___y_5710_;
v___y_5552_ = v___y_5711_;
v___y_5553_ = v___y_5712_;
v___y_5554_ = v___y_5713_;
v___y_5555_ = v___y_5714_;
v___y_5556_ = v___y_5715_;
v___y_5557_ = v___y_5716_;
v___y_5558_ = v___y_5717_;
v___y_5559_ = v___y_5718_;
v___y_5560_ = v___y_5720_;
v___y_5561_ = v___y_5719_;
v___y_5562_ = v___y_5721_;
v___y_5563_ = v___y_5723_;
v___y_5564_ = v___y_5722_;
v_orderedAddInst_x3f_5565_ = v___x_5734_;
v___y_5566_ = v___y_5724_;
v___y_5567_ = v___y_5725_;
v___y_5568_ = v___y_5726_;
v___y_5569_ = v___y_5727_;
v___y_5570_ = v___y_5728_;
v___y_5571_ = v___y_5729_;
v___y_5572_ = v___y_5730_;
v___y_5573_ = v___y_5731_;
v___y_5574_ = v___y_5732_;
v___y_5575_ = v___y_5733_;
goto v___jp_5547_;
}
v___jp_5735_:
{
lean_object* v___x_5761_; 
lean_inc(v___y_5738_);
lean_inc_ref(v_type_5535_);
v___x_5761_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_____do__lift_5750_, v_type_5535_, v___y_5738_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5761_) == 0)
{
lean_object* v_a_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5762_);
lean_dec_ref_known(v___x_5761_, 1);
v___x_5763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
lean_inc_ref(v_type_5535_);
lean_inc(v___y_5745_);
v___x_5764_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_5763_, v___y_5745_, v_type_5535_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5764_) == 0)
{
lean_object* v_a_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; 
v_a_5765_ = lean_ctor_get(v___x_5764_, 0);
lean_inc_n(v_a_5765_, 2);
lean_dec_ref_known(v___x_5764_, 1);
v___x_5766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
lean_inc(v___y_5747_);
lean_inc_n(v___y_5745_, 2);
v___x_5767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___y_5745_);
lean_ctor_set(v___x_5767_, 1, v___y_5747_);
lean_inc_ref(v___x_5767_);
v___x_5768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___y_5745_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = l_Lean_mkConst(v___x_5766_, v___x_5768_);
lean_inc_ref_n(v_type_5535_, 3);
v___x_5770_ = l_Lean_mkApp4(v___x_5769_, v_type_5535_, v_type_5535_, v_type_5535_, v_a_5765_);
v___x_5771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_5770_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5771_) == 0)
{
if (lean_obj_tag(v___y_5738_) == 1)
{
if (lean_obj_tag(v___y_5739_) == 1)
{
lean_object* v_a_5772_; lean_object* v_val_5773_; lean_object* v_val_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; 
v_a_5772_ = lean_ctor_get(v___x_5771_, 0);
lean_inc(v_a_5772_);
lean_dec_ref_known(v___x_5771_, 1);
v_val_5773_ = lean_ctor_get(v___y_5738_, 0);
v_val_5774_ = lean_ctor_get(v___y_5739_, 0);
v___x_5775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__59));
lean_inc_ref(v___y_5736_);
lean_inc_ref(v___y_5749_);
v___x_5776_ = l_Lean_Name_mkStr3(v___y_5749_, v___y_5736_, v___x_5775_);
lean_inc(v___y_5747_);
v___x_5777_ = l_Lean_mkConst(v___x_5776_, v___y_5747_);
lean_inc(v_val_5774_);
lean_inc(v_val_5773_);
lean_inc_ref(v_type_5535_);
v___x_5778_ = l_Lean_mkApp4(v___x_5777_, v_type_5535_, v_a_5765_, v_val_5773_, v_val_5774_);
v___x_5779_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5778_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5779_) == 0)
{
lean_object* v_a_5780_; 
v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
lean_inc(v_a_5780_);
lean_dec_ref_known(v___x_5779_, 1);
v___y_5548_ = v___y_5736_;
v___y_5549_ = v___y_5737_;
v___y_5550_ = v___y_5739_;
v___y_5551_ = v___y_5740_;
v___y_5552_ = v___y_5741_;
v___y_5553_ = v___y_5738_;
v___y_5554_ = v___y_5742_;
v___y_5555_ = v___y_5743_;
v___y_5556_ = v___y_5744_;
v___y_5557_ = v___y_5745_;
v___y_5558_ = v___y_5746_;
v___y_5559_ = v___y_5747_;
v___y_5560_ = v_a_5772_;
v___y_5561_ = v_a_5762_;
v___y_5562_ = v___y_5748_;
v___y_5563_ = v___y_5749_;
v___y_5564_ = v___x_5767_;
v_orderedAddInst_x3f_5565_ = v_a_5780_;
v___y_5566_ = v___y_5751_;
v___y_5567_ = v___y_5752_;
v___y_5568_ = v___y_5753_;
v___y_5569_ = v___y_5754_;
v___y_5570_ = v___y_5755_;
v___y_5571_ = v___y_5756_;
v___y_5572_ = v___y_5757_;
v___y_5573_ = v___y_5758_;
v___y_5574_ = v___y_5759_;
v___y_5575_ = v___y_5760_;
goto v___jp_5547_;
}
else
{
lean_object* v_a_5781_; lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5788_; 
lean_dec(v_a_5772_);
lean_dec_ref_known(v___y_5739_, 1);
lean_dec_ref_known(v___y_5738_, 1);
lean_dec_ref_known(v___x_5767_, 2);
lean_dec(v_a_5762_);
lean_dec(v___y_5747_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec(v___y_5737_);
lean_dec_ref(v_type_5535_);
v_a_5781_ = lean_ctor_get(v___x_5779_, 0);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___x_5779_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5783_ = v___x_5779_;
v_isShared_5784_ = v_isSharedCheck_5788_;
goto v_resetjp_5782_;
}
else
{
lean_inc(v_a_5781_);
lean_dec(v___x_5779_);
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
lean_object* v_a_5789_; 
lean_dec(v_a_5765_);
v_a_5789_ = lean_ctor_get(v___x_5771_, 0);
lean_inc(v_a_5789_);
lean_dec_ref_known(v___x_5771_, 1);
v___y_5707_ = v___y_5736_;
v___y_5708_ = v___y_5737_;
v___y_5709_ = v___y_5739_;
v___y_5710_ = v___y_5740_;
v___y_5711_ = v___y_5741_;
v___y_5712_ = v___y_5738_;
v___y_5713_ = v___y_5742_;
v___y_5714_ = v___y_5743_;
v___y_5715_ = v___y_5744_;
v___y_5716_ = v___y_5745_;
v___y_5717_ = v___y_5746_;
v___y_5718_ = v___y_5747_;
v___y_5719_ = v_a_5762_;
v___y_5720_ = v_a_5789_;
v___y_5721_ = v___y_5748_;
v___y_5722_ = v___x_5767_;
v___y_5723_ = v___y_5749_;
v___y_5724_ = v___y_5751_;
v___y_5725_ = v___y_5752_;
v___y_5726_ = v___y_5753_;
v___y_5727_ = v___y_5754_;
v___y_5728_ = v___y_5755_;
v___y_5729_ = v___y_5756_;
v___y_5730_ = v___y_5757_;
v___y_5731_ = v___y_5758_;
v___y_5732_ = v___y_5759_;
v___y_5733_ = v___y_5760_;
goto v___jp_5706_;
}
}
else
{
lean_object* v_a_5790_; 
lean_dec(v_a_5765_);
v_a_5790_ = lean_ctor_get(v___x_5771_, 0);
lean_inc(v_a_5790_);
lean_dec_ref_known(v___x_5771_, 1);
v___y_5707_ = v___y_5736_;
v___y_5708_ = v___y_5737_;
v___y_5709_ = v___y_5739_;
v___y_5710_ = v___y_5740_;
v___y_5711_ = v___y_5741_;
v___y_5712_ = v___y_5738_;
v___y_5713_ = v___y_5742_;
v___y_5714_ = v___y_5743_;
v___y_5715_ = v___y_5744_;
v___y_5716_ = v___y_5745_;
v___y_5717_ = v___y_5746_;
v___y_5718_ = v___y_5747_;
v___y_5719_ = v_a_5762_;
v___y_5720_ = v_a_5790_;
v___y_5721_ = v___y_5748_;
v___y_5722_ = v___x_5767_;
v___y_5723_ = v___y_5749_;
v___y_5724_ = v___y_5751_;
v___y_5725_ = v___y_5752_;
v___y_5726_ = v___y_5753_;
v___y_5727_ = v___y_5754_;
v___y_5728_ = v___y_5755_;
v___y_5729_ = v___y_5756_;
v___y_5730_ = v___y_5757_;
v___y_5731_ = v___y_5758_;
v___y_5732_ = v___y_5759_;
v___y_5733_ = v___y_5760_;
goto v___jp_5706_;
}
}
else
{
lean_object* v_a_5791_; lean_object* v___x_5793_; uint8_t v_isShared_5794_; uint8_t v_isSharedCheck_5798_; 
lean_dec_ref_known(v___x_5767_, 2);
lean_dec(v_a_5765_);
lean_dec(v_a_5762_);
lean_dec(v___y_5747_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec(v___y_5738_);
lean_dec(v___y_5737_);
lean_dec_ref(v_type_5535_);
v_a_5791_ = lean_ctor_get(v___x_5771_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5771_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5793_ = v___x_5771_;
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
else
{
lean_inc(v_a_5791_);
lean_dec(v___x_5771_);
v___x_5793_ = lean_box(0);
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
v_resetjp_5792_:
{
lean_object* v___x_5796_; 
if (v_isShared_5794_ == 0)
{
v___x_5796_ = v___x_5793_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
lean_dec(v_a_5762_);
lean_dec(v___y_5747_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec(v___y_5738_);
lean_dec(v___y_5737_);
lean_dec_ref(v_type_5535_);
v_a_5799_ = lean_ctor_get(v___x_5764_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5764_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5764_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5764_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
else
{
lean_object* v_a_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5814_; 
lean_dec(v___y_5747_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec(v___y_5738_);
lean_dec(v___y_5737_);
lean_dec_ref(v_type_5535_);
v_a_5807_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5809_ = v___x_5761_;
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_a_5807_);
lean_dec(v___x_5761_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v___x_5812_; 
if (v_isShared_5810_ == 0)
{
v___x_5812_ = v___x_5809_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5807_);
v___x_5812_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
return v___x_5812_;
}
}
}
}
v___jp_5815_:
{
lean_object* v___x_5840_; 
lean_inc(v___y_5818_);
lean_inc(v___y_5821_);
lean_inc_ref(v_type_5535_);
v___x_5840_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_____do__lift_5829_, v_type_5535_, v___y_5821_, v___y_5818_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5840_) == 0)
{
lean_object* v_a_5841_; lean_object* v___x_5842_; 
v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
lean_inc(v_a_5841_);
lean_dec_ref_known(v___x_5840_, 1);
v___x_5842_ = l_Lean_leCarrierIsSort(v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v_a_5843_; uint8_t v___x_5844_; 
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5843_);
lean_dec_ref_known(v___x_5842_, 1);
v___x_5844_ = lean_unbox(v_a_5843_);
lean_dec(v_a_5843_);
if (v___x_5844_ == 0)
{
lean_inc(v___y_5824_);
v___y_5736_ = v___y_5816_;
v___y_5737_ = v___y_5817_;
v___y_5738_ = v___y_5818_;
v___y_5739_ = v___y_5819_;
v___y_5740_ = v_a_5841_;
v___y_5741_ = v___y_5820_;
v___y_5742_ = v___y_5821_;
v___y_5743_ = v___y_5822_;
v___y_5744_ = v___y_5823_;
v___y_5745_ = v___y_5824_;
v___y_5746_ = v___y_5825_;
v___y_5747_ = v___y_5826_;
v___y_5748_ = v___y_5827_;
v___y_5749_ = v___y_5828_;
v_____do__lift_5750_ = v___y_5824_;
v___y_5751_ = v___y_5830_;
v___y_5752_ = v___y_5831_;
v___y_5753_ = v___y_5832_;
v___y_5754_ = v___y_5833_;
v___y_5755_ = v___y_5834_;
v___y_5756_ = v___y_5835_;
v___y_5757_ = v___y_5836_;
v___y_5758_ = v___y_5837_;
v___y_5759_ = v___y_5838_;
v___y_5760_ = v___y_5839_;
goto v___jp_5735_;
}
else
{
lean_object* v___x_5845_; 
lean_inc(v___y_5824_);
v___x_5845_ = l_Lean_Level_succ___override(v___y_5824_);
v___y_5736_ = v___y_5816_;
v___y_5737_ = v___y_5817_;
v___y_5738_ = v___y_5818_;
v___y_5739_ = v___y_5819_;
v___y_5740_ = v_a_5841_;
v___y_5741_ = v___y_5820_;
v___y_5742_ = v___y_5821_;
v___y_5743_ = v___y_5822_;
v___y_5744_ = v___y_5823_;
v___y_5745_ = v___y_5824_;
v___y_5746_ = v___y_5825_;
v___y_5747_ = v___y_5826_;
v___y_5748_ = v___y_5827_;
v___y_5749_ = v___y_5828_;
v_____do__lift_5750_ = v___x_5845_;
v___y_5751_ = v___y_5830_;
v___y_5752_ = v___y_5831_;
v___y_5753_ = v___y_5832_;
v___y_5754_ = v___y_5833_;
v___y_5755_ = v___y_5834_;
v___y_5756_ = v___y_5835_;
v___y_5757_ = v___y_5836_;
v___y_5758_ = v___y_5837_;
v___y_5759_ = v___y_5838_;
v___y_5760_ = v___y_5839_;
goto v___jp_5735_;
}
}
else
{
lean_object* v_a_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5853_; 
lean_dec(v_a_5841_);
lean_dec(v___y_5826_);
lean_dec(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec(v___y_5817_);
lean_dec_ref(v_type_5535_);
v_a_5846_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5848_ = v___x_5842_;
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_a_5846_);
lean_dec(v___x_5842_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5846_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
}
else
{
lean_object* v_a_5854_; lean_object* v___x_5856_; uint8_t v_isShared_5857_; uint8_t v_isSharedCheck_5861_; 
lean_dec(v___y_5826_);
lean_dec(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec(v___y_5817_);
lean_dec_ref(v_type_5535_);
v_a_5854_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5856_ = v___x_5840_;
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
else
{
lean_inc(v_a_5854_);
lean_dec(v___x_5840_);
v___x_5856_ = lean_box(0);
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
v_resetjp_5855_:
{
lean_object* v___x_5859_; 
if (v_isShared_5857_ == 0)
{
v___x_5859_ = v___x_5856_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_a_5854_);
v___x_5859_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
return v___x_5859_;
}
}
}
}
v___jp_5862_:
{
lean_object* v___x_5886_; 
lean_inc(v___y_5868_);
lean_inc_ref(v_type_5535_);
v___x_5886_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_____do__lift_5875_, v_type_5535_, v___y_5868_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
if (lean_obj_tag(v___x_5886_) == 0)
{
lean_object* v_a_5887_; lean_object* v___x_5888_; 
v_a_5887_ = lean_ctor_get(v___x_5886_, 0);
lean_inc(v_a_5887_);
lean_dec_ref_known(v___x_5886_, 1);
v___x_5888_ = l_Lean_leCarrierIsSort(v___y_5884_, v___y_5885_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; uint8_t v___x_5890_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_a_5889_);
lean_dec_ref_known(v___x_5888_, 1);
v___x_5890_ = lean_unbox(v_a_5889_);
lean_dec(v_a_5889_);
if (v___x_5890_ == 0)
{
lean_inc(v___y_5869_);
v___y_5816_ = v___y_5864_;
v___y_5817_ = v___y_5866_;
v___y_5818_ = v___y_5868_;
v___y_5819_ = v_a_5887_;
v___y_5820_ = v___y_5867_;
v___y_5821_ = v___y_5873_;
v___y_5822_ = v___y_5863_;
v___y_5823_ = v___y_5865_;
v___y_5824_ = v___y_5869_;
v___y_5825_ = v___y_5870_;
v___y_5826_ = v___y_5871_;
v___y_5827_ = v___y_5872_;
v___y_5828_ = v___y_5874_;
v_____do__lift_5829_ = v___y_5869_;
v___y_5830_ = v___y_5876_;
v___y_5831_ = v___y_5877_;
v___y_5832_ = v___y_5878_;
v___y_5833_ = v___y_5879_;
v___y_5834_ = v___y_5880_;
v___y_5835_ = v___y_5881_;
v___y_5836_ = v___y_5882_;
v___y_5837_ = v___y_5883_;
v___y_5838_ = v___y_5884_;
v___y_5839_ = v___y_5885_;
goto v___jp_5815_;
}
else
{
lean_object* v___x_5891_; 
lean_inc(v___y_5869_);
v___x_5891_ = l_Lean_Level_succ___override(v___y_5869_);
v___y_5816_ = v___y_5864_;
v___y_5817_ = v___y_5866_;
v___y_5818_ = v___y_5868_;
v___y_5819_ = v_a_5887_;
v___y_5820_ = v___y_5867_;
v___y_5821_ = v___y_5873_;
v___y_5822_ = v___y_5863_;
v___y_5823_ = v___y_5865_;
v___y_5824_ = v___y_5869_;
v___y_5825_ = v___y_5870_;
v___y_5826_ = v___y_5871_;
v___y_5827_ = v___y_5872_;
v___y_5828_ = v___y_5874_;
v_____do__lift_5829_ = v___x_5891_;
v___y_5830_ = v___y_5876_;
v___y_5831_ = v___y_5877_;
v___y_5832_ = v___y_5878_;
v___y_5833_ = v___y_5879_;
v___y_5834_ = v___y_5880_;
v___y_5835_ = v___y_5881_;
v___y_5836_ = v___y_5882_;
v___y_5837_ = v___y_5883_;
v___y_5838_ = v___y_5884_;
v___y_5839_ = v___y_5885_;
goto v___jp_5815_;
}
}
else
{
lean_object* v_a_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5899_; 
lean_dec(v_a_5887_);
lean_dec(v___y_5873_);
lean_dec(v___y_5871_);
lean_dec(v___y_5869_);
lean_dec(v___y_5868_);
lean_dec_ref(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v_type_5535_);
v_a_5892_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5894_ = v___x_5888_;
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_a_5892_);
lean_dec(v___x_5888_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v___x_5897_; 
if (v_isShared_5895_ == 0)
{
v___x_5897_ = v___x_5894_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_dec(v___y_5873_);
lean_dec(v___y_5871_);
lean_dec(v___y_5869_);
lean_dec(v___y_5868_);
lean_dec_ref(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v_type_5535_);
v_a_5900_ = lean_ctor_get(v___x_5886_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5886_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5886_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5886_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
}
v___jp_5908_:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_5535_);
v___x_5932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5931_, v_____do__lift_5920_, v_type_5535_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v_a_5933_; lean_object* v___x_5934_; 
v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5932_, 1);
v___x_5934_ = l_Lean_leCarrierIsSort(v___y_5929_, v___y_5930_);
if (lean_obj_tag(v___x_5934_) == 0)
{
lean_object* v_a_5935_; uint8_t v___x_5936_; 
v_a_5935_ = lean_ctor_get(v___x_5934_, 0);
lean_inc(v_a_5935_);
lean_dec_ref_known(v___x_5934_, 1);
v___x_5936_ = lean_unbox(v_a_5935_);
lean_dec(v_a_5935_);
if (v___x_5936_ == 0)
{
lean_inc(v___y_5915_);
v___y_5863_ = v___y_5910_;
v___y_5864_ = v___y_5909_;
v___y_5865_ = v___y_5912_;
v___y_5866_ = v___y_5911_;
v___y_5867_ = v___y_5914_;
v___y_5868_ = v___y_5913_;
v___y_5869_ = v___y_5915_;
v___y_5870_ = v___y_5916_;
v___y_5871_ = v___y_5917_;
v___y_5872_ = v___y_5918_;
v___y_5873_ = v_a_5933_;
v___y_5874_ = v___y_5919_;
v_____do__lift_5875_ = v___y_5915_;
v___y_5876_ = v___y_5921_;
v___y_5877_ = v___y_5922_;
v___y_5878_ = v___y_5923_;
v___y_5879_ = v___y_5924_;
v___y_5880_ = v___y_5925_;
v___y_5881_ = v___y_5926_;
v___y_5882_ = v___y_5927_;
v___y_5883_ = v___y_5928_;
v___y_5884_ = v___y_5929_;
v___y_5885_ = v___y_5930_;
goto v___jp_5862_;
}
else
{
lean_object* v___x_5937_; 
lean_inc(v___y_5915_);
v___x_5937_ = l_Lean_Level_succ___override(v___y_5915_);
v___y_5863_ = v___y_5910_;
v___y_5864_ = v___y_5909_;
v___y_5865_ = v___y_5912_;
v___y_5866_ = v___y_5911_;
v___y_5867_ = v___y_5914_;
v___y_5868_ = v___y_5913_;
v___y_5869_ = v___y_5915_;
v___y_5870_ = v___y_5916_;
v___y_5871_ = v___y_5917_;
v___y_5872_ = v___y_5918_;
v___y_5873_ = v_a_5933_;
v___y_5874_ = v___y_5919_;
v_____do__lift_5875_ = v___x_5937_;
v___y_5876_ = v___y_5921_;
v___y_5877_ = v___y_5922_;
v___y_5878_ = v___y_5923_;
v___y_5879_ = v___y_5924_;
v___y_5880_ = v___y_5925_;
v___y_5881_ = v___y_5926_;
v___y_5882_ = v___y_5927_;
v___y_5883_ = v___y_5928_;
v___y_5884_ = v___y_5929_;
v___y_5885_ = v___y_5930_;
goto v___jp_5862_;
}
}
else
{
lean_object* v_a_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5945_; 
lean_dec(v_a_5933_);
lean_dec(v___y_5917_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec_ref(v_type_5535_);
v_a_5938_ = lean_ctor_get(v___x_5934_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5934_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5940_ = v___x_5934_;
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_a_5938_);
lean_dec(v___x_5934_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5943_; 
if (v_isShared_5941_ == 0)
{
v___x_5943_ = v___x_5940_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
}
else
{
lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_dec(v___y_5917_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec_ref(v_type_5535_);
v_a_5946_ = lean_ctor_get(v___x_5932_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5932_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5948_ = v___x_5932_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v___x_5932_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
}
v___jp_5954_:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v_type_5535_);
v___x_5977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_5976_, v_____do__lift_5965_, v_type_5535_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_);
if (lean_obj_tag(v___x_5977_) == 0)
{
lean_object* v_a_5978_; lean_object* v___x_5979_; 
v_a_5978_ = lean_ctor_get(v___x_5977_, 0);
lean_inc(v_a_5978_);
lean_dec_ref_known(v___x_5977_, 1);
v___x_5979_ = l_Lean_leCarrierIsSort(v___y_5974_, v___y_5975_);
if (lean_obj_tag(v___x_5979_) == 0)
{
lean_object* v_a_5980_; uint8_t v___x_5981_; 
v_a_5980_ = lean_ctor_get(v___x_5979_, 0);
lean_inc(v_a_5980_);
lean_dec_ref_known(v___x_5979_, 1);
v___x_5981_ = lean_unbox(v_a_5980_);
lean_dec(v_a_5980_);
if (v___x_5981_ == 0)
{
lean_inc(v___y_5960_);
v___y_5909_ = v___y_5956_;
v___y_5910_ = v___y_5955_;
v___y_5911_ = v___y_5958_;
v___y_5912_ = v___y_5957_;
v___y_5913_ = v_a_5978_;
v___y_5914_ = v___y_5959_;
v___y_5915_ = v___y_5960_;
v___y_5916_ = v___y_5961_;
v___y_5917_ = v___y_5962_;
v___y_5918_ = v___y_5963_;
v___y_5919_ = v___y_5964_;
v_____do__lift_5920_ = v___y_5960_;
v___y_5921_ = v___y_5966_;
v___y_5922_ = v___y_5967_;
v___y_5923_ = v___y_5968_;
v___y_5924_ = v___y_5969_;
v___y_5925_ = v___y_5970_;
v___y_5926_ = v___y_5971_;
v___y_5927_ = v___y_5972_;
v___y_5928_ = v___y_5973_;
v___y_5929_ = v___y_5974_;
v___y_5930_ = v___y_5975_;
goto v___jp_5908_;
}
else
{
lean_object* v___x_5982_; 
lean_inc(v___y_5960_);
v___x_5982_ = l_Lean_Level_succ___override(v___y_5960_);
v___y_5909_ = v___y_5956_;
v___y_5910_ = v___y_5955_;
v___y_5911_ = v___y_5958_;
v___y_5912_ = v___y_5957_;
v___y_5913_ = v_a_5978_;
v___y_5914_ = v___y_5959_;
v___y_5915_ = v___y_5960_;
v___y_5916_ = v___y_5961_;
v___y_5917_ = v___y_5962_;
v___y_5918_ = v___y_5963_;
v___y_5919_ = v___y_5964_;
v_____do__lift_5920_ = v___x_5982_;
v___y_5921_ = v___y_5966_;
v___y_5922_ = v___y_5967_;
v___y_5923_ = v___y_5968_;
v___y_5924_ = v___y_5969_;
v___y_5925_ = v___y_5970_;
v___y_5926_ = v___y_5971_;
v___y_5927_ = v___y_5972_;
v___y_5928_ = v___y_5973_;
v___y_5929_ = v___y_5974_;
v___y_5930_ = v___y_5975_;
goto v___jp_5908_;
}
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec(v_a_5978_);
lean_dec(v___y_5962_);
lean_dec(v___y_5960_);
lean_dec_ref(v___y_5959_);
lean_dec(v___y_5958_);
lean_dec_ref(v___y_5957_);
lean_dec_ref(v_type_5535_);
v_a_5983_ = lean_ctor_get(v___x_5979_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5979_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5979_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5979_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec(v___y_5962_);
lean_dec(v___y_5960_);
lean_dec_ref(v___y_5959_);
lean_dec(v___y_5958_);
lean_dec_ref(v___y_5957_);
lean_dec_ref(v_type_5535_);
v_a_5991_ = lean_ctor_get(v___x_5977_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5977_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5977_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5977_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
}
}
}
}
v___jp_5999_:
{
lean_object* v___x_6001_; 
lean_inc_ref(v_type_5535_);
lean_inc(v_val_6000_);
v___x_6001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_val_6000_, v_type_5535_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6001_) == 0)
{
lean_object* v_a_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6059_; 
v_a_6002_ = lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_6001_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6004_ = v___x_6001_;
v_isShared_6005_ = v_isSharedCheck_6059_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_a_6002_);
lean_dec(v___x_6001_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6059_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
if (lean_obj_tag(v_a_6002_) == 1)
{
lean_object* v_val_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
lean_del_object(v___x_6004_);
v_val_6006_ = lean_ctor_get(v_a_6002_, 0);
lean_inc_n(v_val_6006_, 2);
lean_dec_ref_known(v_a_6002_, 1);
v___x_6007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_6008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_6009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_6010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__1));
v___x_6011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_6012_ = lean_box(0);
lean_inc(v_val_6000_);
v___x_6013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6013_, 0, v_val_6000_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
lean_inc_ref(v___x_6013_);
v___x_6014_ = l_Lean_mkConst(v___x_6011_, v___x_6013_);
lean_inc_ref(v_type_5535_);
v___x_6015_ = l_Lean_mkAppB(v___x_6014_, v_type_5535_, v_val_6006_);
v___x_6016_ = l_Lean_Meta_Sym_canon(v___x_6015_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6016_) == 0)
{
lean_object* v_a_6017_; lean_object* v___x_6018_; 
v_a_6017_ = lean_ctor_get(v___x_6016_, 0);
lean_inc(v_a_6017_);
lean_dec_ref_known(v___x_6016_, 1);
v___x_6018_ = l_Lean_Meta_Sym_shareCommon(v_a_6017_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6018_) == 0)
{
lean_object* v_a_6019_; lean_object* v___x_6020_; 
v_a_6019_ = lean_ctor_get(v___x_6018_, 0);
lean_inc_n(v_a_6019_, 2);
lean_dec_ref_known(v___x_6018_, 1);
v___x_6020_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_6019_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6020_) == 0)
{
lean_object* v_a_6021_; 
v_a_6021_ = lean_ctor_get(v___x_6020_, 0);
lean_inc(v_a_6021_);
lean_dec_ref_known(v___x_6020_, 1);
if (lean_obj_tag(v_a_6021_) == 1)
{
lean_object* v_val_6022_; lean_object* v___x_6023_; 
v_val_6022_ = lean_ctor_get(v_a_6021_, 0);
lean_inc(v_val_6022_);
lean_dec_ref_known(v_a_6021_, 1);
v___x_6023_ = l_Lean_leCarrierIsSort(v_a_5544_, v_a_5545_);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_object* v_a_6024_; uint8_t v___x_6025_; 
v_a_6024_ = lean_ctor_get(v___x_6023_, 0);
lean_inc(v_a_6024_);
lean_dec_ref_known(v___x_6023_, 1);
v___x_6025_ = lean_unbox(v_a_6024_);
lean_dec(v_a_6024_);
if (v___x_6025_ == 0)
{
lean_inc(v_val_6000_);
v___y_5955_ = v___x_6010_;
v___y_5956_ = v___x_6008_;
v___y_5957_ = v_a_6019_;
v___y_5958_ = v_val_6022_;
v___y_5959_ = v_val_6006_;
v___y_5960_ = v_val_6000_;
v___y_5961_ = v___x_6012_;
v___y_5962_ = v___x_6013_;
v___y_5963_ = v___x_6009_;
v___y_5964_ = v___x_6007_;
v_____do__lift_5965_ = v_val_6000_;
v___y_5966_ = v_a_5536_;
v___y_5967_ = v_a_5537_;
v___y_5968_ = v_a_5538_;
v___y_5969_ = v_a_5539_;
v___y_5970_ = v_a_5540_;
v___y_5971_ = v_a_5541_;
v___y_5972_ = v_a_5542_;
v___y_5973_ = v_a_5543_;
v___y_5974_ = v_a_5544_;
v___y_5975_ = v_a_5545_;
goto v___jp_5954_;
}
else
{
lean_object* v___x_6026_; 
lean_inc(v_val_6000_);
v___x_6026_ = l_Lean_Level_succ___override(v_val_6000_);
v___y_5955_ = v___x_6010_;
v___y_5956_ = v___x_6008_;
v___y_5957_ = v_a_6019_;
v___y_5958_ = v_val_6022_;
v___y_5959_ = v_val_6006_;
v___y_5960_ = v_val_6000_;
v___y_5961_ = v___x_6012_;
v___y_5962_ = v___x_6013_;
v___y_5963_ = v___x_6009_;
v___y_5964_ = v___x_6007_;
v_____do__lift_5965_ = v___x_6026_;
v___y_5966_ = v_a_5536_;
v___y_5967_ = v_a_5537_;
v___y_5968_ = v_a_5538_;
v___y_5969_ = v_a_5539_;
v___y_5970_ = v_a_5540_;
v___y_5971_ = v_a_5541_;
v___y_5972_ = v_a_5542_;
v___y_5973_ = v_a_5543_;
v___y_5974_ = v_a_5544_;
v___y_5975_ = v_a_5545_;
goto v___jp_5954_;
}
}
else
{
lean_object* v_a_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6034_; 
lean_dec(v_val_6022_);
lean_dec(v_a_6019_);
lean_dec_ref_known(v___x_6013_, 2);
lean_dec(v_val_6006_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v_a_6027_ = lean_ctor_get(v___x_6023_, 0);
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6034_ == 0)
{
v___x_6029_ = v___x_6023_;
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_a_6027_);
lean_dec(v___x_6023_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v___x_6032_; 
if (v_isShared_6030_ == 0)
{
v___x_6032_ = v___x_6029_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_a_6027_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
}
else
{
lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
lean_dec(v_a_6021_);
lean_dec_ref_known(v___x_6013_, 2);
lean_dec(v_val_6006_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v___x_6035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6);
v___x_6036_ = l_Lean_indentExpr(v_a_6019_);
v___x_6037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6035_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_6037_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_);
return v___x_6038_;
}
}
else
{
lean_dec(v_a_6019_);
lean_dec_ref_known(v___x_6013_, 2);
lean_dec(v_val_6006_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
return v___x_6020_;
}
}
else
{
lean_object* v_a_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6046_; 
lean_dec_ref_known(v___x_6013_, 2);
lean_dec(v_val_6006_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v_a_6039_ = lean_ctor_get(v___x_6018_, 0);
v_isSharedCheck_6046_ = !lean_is_exclusive(v___x_6018_);
if (v_isSharedCheck_6046_ == 0)
{
v___x_6041_ = v___x_6018_;
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_a_6039_);
lean_dec(v___x_6018_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
lean_object* v___x_6044_; 
if (v_isShared_6042_ == 0)
{
v___x_6044_ = v___x_6041_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v_a_6039_);
v___x_6044_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
return v___x_6044_;
}
}
}
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6054_; 
lean_dec_ref_known(v___x_6013_, 2);
lean_dec(v_val_6006_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v_a_6047_ = lean_ctor_get(v___x_6016_, 0);
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_6016_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6049_ = v___x_6016_;
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_dec(v___x_6016_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6052_; 
if (v_isShared_6050_ == 0)
{
v___x_6052_ = v___x_6049_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
}
}
}
}
else
{
lean_object* v___x_6055_; lean_object* v___x_6057_; 
lean_dec(v_a_6002_);
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v___x_6055_ = lean_box(0);
if (v_isShared_6005_ == 0)
{
lean_ctor_set(v___x_6004_, 0, v___x_6055_);
v___x_6057_ = v___x_6004_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v___x_6055_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
else
{
lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
lean_dec(v_val_6000_);
lean_dec_ref(v_type_5535_);
v_a_6060_ = lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6001_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6062_ = v___x_6001_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_dec(v___x_6001_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_){
_start:
{
lean_object* v_res_6120_; 
v_res_6120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_6108_, v_a_6109_, v_a_6110_, v_a_6111_, v_a_6112_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_);
lean_dec(v_a_6118_);
lean_dec_ref(v_a_6117_);
lean_dec(v_a_6116_);
lean_dec_ref(v_a_6115_);
lean_dec(v_a_6114_);
lean_dec_ref(v_a_6113_);
lean_dec(v_a_6112_);
lean_dec_ref(v_a_6111_);
lean_dec(v_a_6110_);
lean_dec(v_a_6109_);
return v_res_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_6121_, lean_object* v_msg_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_){
_start:
{
lean_object* v___x_6134_; 
v___x_6134_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_6122_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_6135_, lean_object* v_msg_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_){
_start:
{
lean_object* v_res_6148_; 
v_res_6148_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_6135_, v_msg_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_);
lean_dec(v___y_6146_);
lean_dec_ref(v___y_6145_);
lean_dec(v___y_6144_);
lean_dec_ref(v___y_6143_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec(v___y_6137_);
return v_res_6148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_6149_, lean_object* v_a_6150_, lean_object* v_s_6151_){
_start:
{
lean_object* v_structs_6152_; lean_object* v_typeIdOf_6153_; lean_object* v_exprToStructId_6154_; lean_object* v_exprToStructIdEntries_6155_; lean_object* v_forbiddenNatModules_6156_; lean_object* v_natStructs_6157_; lean_object* v_natTypeIdOf_6158_; lean_object* v_exprToNatStructId_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6167_; 
v_structs_6152_ = lean_ctor_get(v_s_6151_, 0);
v_typeIdOf_6153_ = lean_ctor_get(v_s_6151_, 1);
v_exprToStructId_6154_ = lean_ctor_get(v_s_6151_, 2);
v_exprToStructIdEntries_6155_ = lean_ctor_get(v_s_6151_, 3);
v_forbiddenNatModules_6156_ = lean_ctor_get(v_s_6151_, 4);
v_natStructs_6157_ = lean_ctor_get(v_s_6151_, 5);
v_natTypeIdOf_6158_ = lean_ctor_get(v_s_6151_, 6);
v_exprToNatStructId_6159_ = lean_ctor_get(v_s_6151_, 7);
v_isSharedCheck_6167_ = !lean_is_exclusive(v_s_6151_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6161_ = v_s_6151_;
v_isShared_6162_ = v_isSharedCheck_6167_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_exprToNatStructId_6159_);
lean_inc(v_natTypeIdOf_6158_);
lean_inc(v_natStructs_6157_);
lean_inc(v_forbiddenNatModules_6156_);
lean_inc(v_exprToStructIdEntries_6155_);
lean_inc(v_exprToStructId_6154_);
lean_inc(v_typeIdOf_6153_);
lean_inc(v_structs_6152_);
lean_dec(v_s_6151_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6167_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6163_; lean_object* v___x_6165_; 
v___x_6163_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_6158_, v_type_6149_, v_a_6150_);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 6, v___x_6163_);
v___x_6165_ = v___x_6161_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_structs_6152_);
lean_ctor_set(v_reuseFailAlloc_6166_, 1, v_typeIdOf_6153_);
lean_ctor_set(v_reuseFailAlloc_6166_, 2, v_exprToStructId_6154_);
lean_ctor_set(v_reuseFailAlloc_6166_, 3, v_exprToStructIdEntries_6155_);
lean_ctor_set(v_reuseFailAlloc_6166_, 4, v_forbiddenNatModules_6156_);
lean_ctor_set(v_reuseFailAlloc_6166_, 5, v_natStructs_6157_);
lean_ctor_set(v_reuseFailAlloc_6166_, 6, v___x_6163_);
lean_ctor_set(v_reuseFailAlloc_6166_, 7, v_exprToNatStructId_6159_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_6168_, lean_object* v_i_6169_, lean_object* v_k_6170_){
_start:
{
lean_object* v___x_6171_; uint8_t v___x_6172_; 
v___x_6171_ = lean_array_get_size(v_keys_6168_);
v___x_6172_ = lean_nat_dec_lt(v_i_6169_, v___x_6171_);
if (v___x_6172_ == 0)
{
lean_dec(v_i_6169_);
return v___x_6172_;
}
else
{
lean_object* v_k_x27_6173_; size_t v___x_6174_; size_t v___x_6175_; uint8_t v___x_6176_; 
v_k_x27_6173_ = lean_array_fget_borrowed(v_keys_6168_, v_i_6169_);
v___x_6174_ = lean_ptr_addr(v_k_6170_);
v___x_6175_ = lean_ptr_addr(v_k_x27_6173_);
v___x_6176_ = lean_usize_dec_eq(v___x_6174_, v___x_6175_);
if (v___x_6176_ == 0)
{
lean_object* v___x_6177_; lean_object* v___x_6178_; 
v___x_6177_ = lean_unsigned_to_nat(1u);
v___x_6178_ = lean_nat_add(v_i_6169_, v___x_6177_);
lean_dec(v_i_6169_);
v_i_6169_ = v___x_6178_;
goto _start;
}
else
{
lean_dec(v_i_6169_);
return v___x_6172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_6180_, lean_object* v_i_6181_, lean_object* v_k_6182_){
_start:
{
uint8_t v_res_6183_; lean_object* v_r_6184_; 
v_res_6183_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_6180_, v_i_6181_, v_k_6182_);
lean_dec_ref(v_k_6182_);
lean_dec_ref(v_keys_6180_);
v_r_6184_ = lean_box(v_res_6183_);
return v_r_6184_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_6185_, size_t v_x_6186_, lean_object* v_x_6187_){
_start:
{
if (lean_obj_tag(v_x_6185_) == 0)
{
lean_object* v_es_6188_; lean_object* v___x_6189_; size_t v___x_6190_; size_t v___x_6191_; lean_object* v_j_6192_; lean_object* v___x_6193_; 
v_es_6188_ = lean_ctor_get(v_x_6185_, 0);
v___x_6189_ = lean_box(2);
v___x_6190_ = ((size_t)31ULL);
v___x_6191_ = lean_usize_land(v_x_6186_, v___x_6190_);
v_j_6192_ = lean_usize_to_nat(v___x_6191_);
v___x_6193_ = lean_array_get_borrowed(v___x_6189_, v_es_6188_, v_j_6192_);
lean_dec(v_j_6192_);
switch(lean_obj_tag(v___x_6193_))
{
case 0:
{
lean_object* v_key_6194_; size_t v___x_6195_; size_t v___x_6196_; uint8_t v___x_6197_; 
v_key_6194_ = lean_ctor_get(v___x_6193_, 0);
v___x_6195_ = lean_ptr_addr(v_x_6187_);
v___x_6196_ = lean_ptr_addr(v_key_6194_);
v___x_6197_ = lean_usize_dec_eq(v___x_6195_, v___x_6196_);
return v___x_6197_;
}
case 1:
{
lean_object* v_node_6198_; size_t v___x_6199_; size_t v___x_6200_; 
v_node_6198_ = lean_ctor_get(v___x_6193_, 0);
v___x_6199_ = ((size_t)5ULL);
v___x_6200_ = lean_usize_shift_right(v_x_6186_, v___x_6199_);
v_x_6185_ = v_node_6198_;
v_x_6186_ = v___x_6200_;
goto _start;
}
default: 
{
uint8_t v___x_6202_; 
v___x_6202_ = 0;
return v___x_6202_;
}
}
}
else
{
lean_object* v_ks_6203_; lean_object* v___x_6204_; uint8_t v___x_6205_; 
v_ks_6203_ = lean_ctor_get(v_x_6185_, 0);
v___x_6204_ = lean_unsigned_to_nat(0u);
v___x_6205_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_6203_, v___x_6204_, v_x_6187_);
return v___x_6205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_6206_, lean_object* v_x_6207_, lean_object* v_x_6208_){
_start:
{
size_t v_x_8678__boxed_6209_; uint8_t v_res_6210_; lean_object* v_r_6211_; 
v_x_8678__boxed_6209_ = lean_unbox_usize(v_x_6207_);
lean_dec(v_x_6207_);
v_res_6210_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6206_, v_x_8678__boxed_6209_, v_x_6208_);
lean_dec_ref(v_x_6208_);
lean_dec_ref(v_x_6206_);
v_r_6211_ = lean_box(v_res_6210_);
return v_r_6211_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_6212_, lean_object* v_x_6213_){
_start:
{
size_t v___x_6214_; size_t v___x_6215_; size_t v___x_6216_; uint64_t v___x_6217_; size_t v___x_6218_; uint8_t v___x_6219_; 
v___x_6214_ = lean_ptr_addr(v_x_6213_);
v___x_6215_ = ((size_t)3ULL);
v___x_6216_ = lean_usize_shift_right(v___x_6214_, v___x_6215_);
v___x_6217_ = lean_usize_to_uint64(v___x_6216_);
v___x_6218_ = lean_uint64_to_usize(v___x_6217_);
v___x_6219_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6212_, v___x_6218_, v_x_6213_);
return v___x_6219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_6220_, lean_object* v_x_6221_){
_start:
{
uint8_t v_res_6222_; lean_object* v_r_6223_; 
v_res_6222_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_6220_, v_x_6221_);
lean_dec_ref(v_x_6221_);
lean_dec_ref(v_x_6220_);
v_r_6223_ = lean_box(v_res_6222_);
return v_r_6223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_6227_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v_a_6237_; lean_object* v___x_6239_; uint8_t v_isShared_6240_; uint8_t v_isSharedCheck_6326_; 
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6326_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6326_ == 0)
{
v___x_6239_ = v___x_6236_;
v_isShared_6240_ = v_isSharedCheck_6326_;
goto v_resetjp_6238_;
}
else
{
lean_inc(v_a_6237_);
lean_dec(v___x_6236_);
v___x_6239_ = lean_box(0);
v_isShared_6240_ = v_isSharedCheck_6326_;
goto v_resetjp_6238_;
}
v_resetjp_6238_:
{
uint8_t v_linarith_6241_; 
v_linarith_6241_ = lean_ctor_get_uint8(v_a_6237_, sizeof(void*)*18 + 23);
lean_dec(v_a_6237_);
if (v_linarith_6241_ == 0)
{
lean_object* v___x_6242_; lean_object* v___x_6244_; 
lean_dec_ref(v_type_6224_);
v___x_6242_ = lean_box(0);
if (v_isShared_6240_ == 0)
{
lean_ctor_set(v___x_6239_, 0, v___x_6242_);
v___x_6244_ = v___x_6239_;
goto v_reusejp_6243_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v___x_6242_);
v___x_6244_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6243_;
}
v_reusejp_6243_:
{
return v___x_6244_;
}
}
else
{
lean_object* v___x_6246_; 
lean_del_object(v___x_6239_);
v___x_6246_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6225_, v_a_6233_);
if (lean_obj_tag(v___x_6246_) == 0)
{
lean_object* v_a_6247_; lean_object* v___x_6249_; uint8_t v_isShared_6250_; uint8_t v_isSharedCheck_6317_; 
v_a_6247_ = lean_ctor_get(v___x_6246_, 0);
v_isSharedCheck_6317_ = !lean_is_exclusive(v___x_6246_);
if (v_isSharedCheck_6317_ == 0)
{
v___x_6249_ = v___x_6246_;
v_isShared_6250_ = v_isSharedCheck_6317_;
goto v_resetjp_6248_;
}
else
{
lean_inc(v_a_6247_);
lean_dec(v___x_6246_);
v___x_6249_ = lean_box(0);
v_isShared_6250_ = v_isSharedCheck_6317_;
goto v_resetjp_6248_;
}
v_resetjp_6248_:
{
lean_object* v_forbiddenNatModules_6251_; uint8_t v___x_6252_; 
v_forbiddenNatModules_6251_ = lean_ctor_get(v_a_6247_, 4);
lean_inc_ref(v_forbiddenNatModules_6251_);
lean_dec(v_a_6247_);
v___x_6252_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_6251_, v_type_6224_);
lean_dec_ref(v_forbiddenNatModules_6251_);
if (v___x_6252_ == 0)
{
lean_object* v___x_6253_; 
lean_del_object(v___x_6249_);
lean_inc_ref(v_type_6224_);
v___x_6253_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_type_6224_, v_a_6227_, v_a_6232_);
if (lean_obj_tag(v___x_6253_) == 0)
{
lean_object* v_a_6254_; lean_object* v___x_6256_; uint8_t v_isShared_6257_; uint8_t v_isSharedCheck_6304_; 
v_a_6254_ = lean_ctor_get(v___x_6253_, 0);
v_isSharedCheck_6304_ = !lean_is_exclusive(v___x_6253_);
if (v_isSharedCheck_6304_ == 0)
{
v___x_6256_ = v___x_6253_;
v_isShared_6257_ = v_isSharedCheck_6304_;
goto v_resetjp_6255_;
}
else
{
lean_inc(v_a_6254_);
lean_dec(v___x_6253_);
v___x_6256_ = lean_box(0);
v_isShared_6257_ = v_isSharedCheck_6304_;
goto v_resetjp_6255_;
}
v_resetjp_6255_:
{
uint8_t v___x_6258_; 
v___x_6258_ = lean_unbox(v_a_6254_);
lean_dec(v_a_6254_);
if (v___x_6258_ == 0)
{
lean_object* v___x_6259_; 
lean_del_object(v___x_6256_);
v___x_6259_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6225_, v_a_6233_);
if (lean_obj_tag(v___x_6259_) == 0)
{
lean_object* v_a_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6291_; 
v_a_6260_ = lean_ctor_get(v___x_6259_, 0);
v_isSharedCheck_6291_ = !lean_is_exclusive(v___x_6259_);
if (v_isSharedCheck_6291_ == 0)
{
v___x_6262_ = v___x_6259_;
v_isShared_6263_ = v_isSharedCheck_6291_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_a_6260_);
lean_dec(v___x_6259_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6291_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v_natTypeIdOf_6264_; lean_object* v___x_6265_; 
v_natTypeIdOf_6264_ = lean_ctor_get(v_a_6260_, 6);
lean_inc_ref(v_natTypeIdOf_6264_);
lean_dec(v_a_6260_);
v___x_6265_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_6264_, v_type_6224_);
lean_dec_ref(v_natTypeIdOf_6264_);
if (lean_obj_tag(v___x_6265_) == 1)
{
lean_object* v_val_6266_; lean_object* v___x_6268_; 
lean_dec_ref(v_type_6224_);
v_val_6266_ = lean_ctor_get(v___x_6265_, 0);
lean_inc(v_val_6266_);
lean_dec_ref_known(v___x_6265_, 1);
if (v_isShared_6263_ == 0)
{
lean_ctor_set(v___x_6262_, 0, v_val_6266_);
v___x_6268_ = v___x_6262_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_val_6266_);
v___x_6268_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
return v___x_6268_;
}
}
else
{
lean_object* v___x_6270_; 
lean_dec(v___x_6265_);
lean_del_object(v___x_6262_);
lean_inc_ref(v_type_6224_);
v___x_6270_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_6224_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_, v_a_6232_, v_a_6233_, v_a_6234_);
if (lean_obj_tag(v___x_6270_) == 0)
{
lean_object* v_a_6271_; lean_object* v___f_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; 
v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
lean_inc_n(v_a_6271_, 2);
lean_dec_ref_known(v___x_6270_, 1);
v___f_6272_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_6272_, 0, v_type_6224_);
lean_closure_set(v___f_6272_, 1, v_a_6271_);
v___x_6273_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_6274_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6273_, v___f_6272_, v_a_6225_);
if (lean_obj_tag(v___x_6274_) == 0)
{
lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6281_; 
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6274_);
if (v_isSharedCheck_6281_ == 0)
{
lean_object* v_unused_6282_; 
v_unused_6282_ = lean_ctor_get(v___x_6274_, 0);
lean_dec(v_unused_6282_);
v___x_6276_ = v___x_6274_;
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
else
{
lean_dec(v___x_6274_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___x_6279_; 
if (v_isShared_6277_ == 0)
{
lean_ctor_set(v___x_6276_, 0, v_a_6271_);
v___x_6279_ = v___x_6276_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v_a_6271_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
else
{
lean_object* v_a_6283_; lean_object* v___x_6285_; uint8_t v_isShared_6286_; uint8_t v_isSharedCheck_6290_; 
lean_dec(v_a_6271_);
v_a_6283_ = lean_ctor_get(v___x_6274_, 0);
v_isSharedCheck_6290_ = !lean_is_exclusive(v___x_6274_);
if (v_isSharedCheck_6290_ == 0)
{
v___x_6285_ = v___x_6274_;
v_isShared_6286_ = v_isSharedCheck_6290_;
goto v_resetjp_6284_;
}
else
{
lean_inc(v_a_6283_);
lean_dec(v___x_6274_);
v___x_6285_ = lean_box(0);
v_isShared_6286_ = v_isSharedCheck_6290_;
goto v_resetjp_6284_;
}
v_resetjp_6284_:
{
lean_object* v___x_6288_; 
if (v_isShared_6286_ == 0)
{
v___x_6288_ = v___x_6285_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6289_; 
v_reuseFailAlloc_6289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6289_, 0, v_a_6283_);
v___x_6288_ = v_reuseFailAlloc_6289_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
return v___x_6288_;
}
}
}
}
else
{
lean_dec_ref(v_type_6224_);
return v___x_6270_;
}
}
}
}
else
{
lean_object* v_a_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6299_; 
lean_dec_ref(v_type_6224_);
v_a_6292_ = lean_ctor_get(v___x_6259_, 0);
v_isSharedCheck_6299_ = !lean_is_exclusive(v___x_6259_);
if (v_isSharedCheck_6299_ == 0)
{
v___x_6294_ = v___x_6259_;
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_a_6292_);
lean_dec(v___x_6259_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6297_; 
if (v_isShared_6295_ == 0)
{
v___x_6297_ = v___x_6294_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6298_; 
v_reuseFailAlloc_6298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6292_);
v___x_6297_ = v_reuseFailAlloc_6298_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
return v___x_6297_;
}
}
}
}
else
{
lean_object* v___x_6300_; lean_object* v___x_6302_; 
lean_dec_ref(v_type_6224_);
v___x_6300_ = lean_box(0);
if (v_isShared_6257_ == 0)
{
lean_ctor_set(v___x_6256_, 0, v___x_6300_);
v___x_6302_ = v___x_6256_;
goto v_reusejp_6301_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v___x_6300_);
v___x_6302_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6301_;
}
v_reusejp_6301_:
{
return v___x_6302_;
}
}
}
}
else
{
lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6312_; 
lean_dec_ref(v_type_6224_);
v_a_6305_ = lean_ctor_get(v___x_6253_, 0);
v_isSharedCheck_6312_ = !lean_is_exclusive(v___x_6253_);
if (v_isSharedCheck_6312_ == 0)
{
v___x_6307_ = v___x_6253_;
v_isShared_6308_ = v_isSharedCheck_6312_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6253_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6312_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
lean_object* v___x_6310_; 
if (v_isShared_6308_ == 0)
{
v___x_6310_ = v___x_6307_;
goto v_reusejp_6309_;
}
else
{
lean_object* v_reuseFailAlloc_6311_; 
v_reuseFailAlloc_6311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_a_6305_);
v___x_6310_ = v_reuseFailAlloc_6311_;
goto v_reusejp_6309_;
}
v_reusejp_6309_:
{
return v___x_6310_;
}
}
}
}
else
{
lean_object* v___x_6313_; lean_object* v___x_6315_; 
lean_dec_ref(v_type_6224_);
v___x_6313_ = lean_box(0);
if (v_isShared_6250_ == 0)
{
lean_ctor_set(v___x_6249_, 0, v___x_6313_);
v___x_6315_ = v___x_6249_;
goto v_reusejp_6314_;
}
else
{
lean_object* v_reuseFailAlloc_6316_; 
v_reuseFailAlloc_6316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6316_, 0, v___x_6313_);
v___x_6315_ = v_reuseFailAlloc_6316_;
goto v_reusejp_6314_;
}
v_reusejp_6314_:
{
return v___x_6315_;
}
}
}
}
else
{
lean_object* v_a_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6325_; 
lean_dec_ref(v_type_6224_);
v_a_6318_ = lean_ctor_get(v___x_6246_, 0);
v_isSharedCheck_6325_ = !lean_is_exclusive(v___x_6246_);
if (v_isSharedCheck_6325_ == 0)
{
v___x_6320_ = v___x_6246_;
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_a_6318_);
lean_dec(v___x_6246_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6323_; 
if (v_isShared_6321_ == 0)
{
v___x_6323_ = v___x_6320_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6324_; 
v_reuseFailAlloc_6324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6324_, 0, v_a_6318_);
v___x_6323_ = v_reuseFailAlloc_6324_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
return v___x_6323_;
}
}
}
}
}
}
else
{
lean_object* v_a_6327_; lean_object* v___x_6329_; uint8_t v_isShared_6330_; uint8_t v_isSharedCheck_6334_; 
lean_dec_ref(v_type_6224_);
v_a_6327_ = lean_ctor_get(v___x_6236_, 0);
v_isSharedCheck_6334_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6334_ == 0)
{
v___x_6329_ = v___x_6236_;
v_isShared_6330_ = v_isSharedCheck_6334_;
goto v_resetjp_6328_;
}
else
{
lean_inc(v_a_6327_);
lean_dec(v___x_6236_);
v___x_6329_ = lean_box(0);
v_isShared_6330_ = v_isSharedCheck_6334_;
goto v_resetjp_6328_;
}
v_resetjp_6328_:
{
lean_object* v___x_6332_; 
if (v_isShared_6330_ == 0)
{
v___x_6332_ = v___x_6329_;
goto v_reusejp_6331_;
}
else
{
lean_object* v_reuseFailAlloc_6333_; 
v_reuseFailAlloc_6333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_a_6327_);
v___x_6332_ = v_reuseFailAlloc_6333_;
goto v_reusejp_6331_;
}
v_reusejp_6331_:
{
return v___x_6332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_){
_start:
{
lean_object* v_res_6347_; 
v_res_6347_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_, v_a_6345_);
lean_dec(v_a_6345_);
lean_dec_ref(v_a_6344_);
lean_dec(v_a_6343_);
lean_dec_ref(v_a_6342_);
lean_dec(v_a_6341_);
lean_dec_ref(v_a_6340_);
lean_dec(v_a_6339_);
lean_dec_ref(v_a_6338_);
lean_dec(v_a_6337_);
lean_dec(v_a_6336_);
return v_res_6347_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_6348_, lean_object* v_x_6349_, lean_object* v_x_6350_){
_start:
{
uint8_t v___x_6351_; 
v___x_6351_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_6349_, v_x_6350_);
return v___x_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_6352_, lean_object* v_x_6353_, lean_object* v_x_6354_){
_start:
{
uint8_t v_res_6355_; lean_object* v_r_6356_; 
v_res_6355_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_6352_, v_x_6353_, v_x_6354_);
lean_dec_ref(v_x_6354_);
lean_dec_ref(v_x_6353_);
v_r_6356_ = lean_box(v_res_6355_);
return v_r_6356_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_6357_, lean_object* v_x_6358_, size_t v_x_6359_, lean_object* v_x_6360_){
_start:
{
uint8_t v___x_6361_; 
v___x_6361_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_6358_, v_x_6359_, v_x_6360_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6362_, lean_object* v_x_6363_, lean_object* v_x_6364_, lean_object* v_x_6365_){
_start:
{
size_t v_x_8946__boxed_6366_; uint8_t v_res_6367_; lean_object* v_r_6368_; 
v_x_8946__boxed_6366_ = lean_unbox_usize(v_x_6364_);
lean_dec(v_x_6364_);
v_res_6367_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_6362_, v_x_6363_, v_x_8946__boxed_6366_, v_x_6365_);
lean_dec_ref(v_x_6365_);
lean_dec_ref(v_x_6363_);
v_r_6368_ = lean_box(v_res_6367_);
return v_r_6368_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_6369_, lean_object* v_keys_6370_, lean_object* v_vals_6371_, lean_object* v_heq_6372_, lean_object* v_i_6373_, lean_object* v_k_6374_){
_start:
{
uint8_t v___x_6375_; 
v___x_6375_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_6370_, v_i_6373_, v_k_6374_);
return v___x_6375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_6376_, lean_object* v_keys_6377_, lean_object* v_vals_6378_, lean_object* v_heq_6379_, lean_object* v_i_6380_, lean_object* v_k_6381_){
_start:
{
uint8_t v_res_6382_; lean_object* v_r_6383_; 
v_res_6382_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_6376_, v_keys_6377_, v_vals_6378_, v_heq_6379_, v_i_6380_, v_k_6381_);
lean_dec_ref(v_k_6381_);
lean_dec_ref(v_vals_6378_);
lean_dec_ref(v_keys_6377_);
v_r_6383_ = lean_box(v_res_6382_);
return v_r_6383_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
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
res = initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
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
