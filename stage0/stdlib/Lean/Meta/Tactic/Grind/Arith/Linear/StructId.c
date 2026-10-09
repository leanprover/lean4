// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.StructId
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.Linear.Var import Lean.Meta.Sym.Arith.Insts import Init.Grind.Module.Envelope
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(lean_object* v_type_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_798_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; uint8_t v_lia_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v_lia_807_ = lean_ctor_get_uint8(v_a_806_, sizeof(void*)*14 + 23);
lean_dec(v_a_806_);
if (v_lia_807_ == 0)
{
lean_dec_ref(v_type_797_);
goto v___jp_801_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_797_, v_a_799_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_818_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_818_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_818_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; 
v___x_813_ = lean_unbox(v_a_809_);
lean_dec(v_a_809_);
if (v___x_813_ == 0)
{
lean_del_object(v___x_811_);
goto v___jp_801_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_box(v_lia_807_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_814_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_type_797_);
v_a_819_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_805_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_805_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
v___jp_801_:
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = 0;
v___x_803_ = lean_box(v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg___boxed(lean_object* v_type_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(lean_object* v_type_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_832_, v_a_835_, v_a_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___boxed(lean_object* v_type_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType(v_type_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec(v_a_846_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(lean_object* v_ringId_x3f_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_858_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_897_; 
v_val_870_ = lean_ctor_get(v_ringId_x3f_858_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_ringId_x3f_858_);
if (v_isSharedCheck_897_ == 0)
{
v___x_872_ = v_ringId_x3f_858_;
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v_ringId_x3f_858_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = 0;
v___x_875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_875_, 0, v_val_870_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*1, v___x_874_);
v___x_876_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_875_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec_ref_known(v___x_875_, 1);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_commRingInst_881_; lean_object* v___x_883_; 
v_commRingInst_881_ = lean_ctor_get(v_a_877_, 5);
lean_inc_ref(v_commRingInst_881_);
lean_dec(v_a_877_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_commRingInst_881_);
v___x_883_ = v___x_872_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_commRingInst_881_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_872_);
v_a_889_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_876_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_876_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_ringId_x3f_858_);
v___x_898_ = lean_box(0);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f___boxed(lean_object* v_ringId_x3f_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_ringId_x3f_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(lean_object* v_u_927_, lean_object* v_type_928_, lean_object* v_commRingInst_x3f_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
if (lean_obj_tag(v_commRingInst_x3f_929_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_949_; 
v_val_936_ = lean_ctor_get(v_commRingInst_x3f_929_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_commRingInst_x3f_929_);
if (v_isSharedCheck_949_ == 0)
{
v___x_938_ = v_commRingInst_x3f_929_;
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v_commRingInst_x3f_929_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__4));
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v_u_927_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_mkConst(v___x_940_, v___x_942_);
v___x_944_ = l_Lean_mkAppB(v___x_943_, v_type_928_, v_val_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_944_);
v___x_946_ = v___x_938_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_commRingInst_x3f_929_);
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__6));
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_952_, 0, v_u_927_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_mkConst(v___x_950_, v___x_952_);
v___x_954_ = l_Lean_Expr_app___override(v___x_953_, v_type_928_);
v___x_955_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_954_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___boxed(lean_object* v_u_956_, lean_object* v_type_957_, lean_object* v_commRingInst_x3f_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_956_, v_type_957_, v_commRingInst_x3f_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(lean_object* v_u_966_, lean_object* v_type_967_, lean_object* v_commRingInst_x3f_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_u_966_, v_type_967_, v_commRingInst_x3f_968_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___boxed(lean_object* v_u_981_, lean_object* v_type_982_, lean_object* v_commRingInst_x3f_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f(v_u_981_, v_type_982_, v_commRingInst_x3f_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec(v_a_984_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(lean_object* v_u_1007_, lean_object* v_type_1008_, lean_object* v_ringInst_x3f_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1009_) == 1)
{
lean_object* v_val_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1029_; 
v_val_1016_ = lean_ctor_get(v_ringInst_x3f_1009_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_ringInst_x3f_1009_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1018_ = v_ringInst_x3f_1009_;
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_val_1016_);
lean_dec(v_ringInst_x3f_1009_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__1));
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_u_1007_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_mkConst(v___x_1020_, v___x_1022_);
v___x_1024_ = l_Lean_mkAppB(v___x_1023_, v_type_1008_, v_val_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1024_);
v___x_1026_ = v___x_1018_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_ringInst_x3f_1009_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_u_1007_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_mkConst(v___x_1030_, v___x_1032_);
v___x_1034_ = l_Lean_Expr_app___override(v___x_1033_, v_type_1008_);
v___x_1035_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1034_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___boxed(lean_object* v_u_1036_, lean_object* v_type_1037_, lean_object* v_ringInst_x3f_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1036_, v_type_1037_, v_ringInst_x3f_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(lean_object* v_u_1046_, lean_object* v_type_1047_, lean_object* v_ringInst_x3f_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_u_1046_, v_type_1047_, v_ringInst_x3f_1048_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___boxed(lean_object* v_u_1061_, lean_object* v_type_1062_, lean_object* v_ringInst_x3f_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f(v_u_1061_, v_type_1062_, v_ringInst_x3f_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(lean_object* v_u_1087_, lean_object* v_type_1088_, lean_object* v_ringInst_x3f_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
if (lean_obj_tag(v_ringInst_x3f_1089_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1109_; 
v_val_1096_ = lean_ctor_get(v_ringInst_x3f_1089_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_ringInst_x3f_1089_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1098_ = v_ringInst_x3f_1089_;
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_val_1096_);
lean_dec(v_ringInst_x3f_1089_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1109_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__1));
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_u_1087_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_mkConst(v___x_1100_, v___x_1102_);
v___x_1104_ = l_Lean_mkAppB(v___x_1103_, v_type_1088_, v_val_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1104_);
v___x_1106_ = v___x_1098_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_ringInst_x3f_1089_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___closed__3));
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v_u_1087_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_mkConst(v___x_1110_, v___x_1112_);
v___x_1114_ = l_Lean_Expr_app___override(v___x_1113_, v_type_1088_);
v___x_1115_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1114_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg___boxed(lean_object* v_u_1116_, lean_object* v_type_1117_, lean_object* v_ringInst_x3f_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1116_, v_type_1117_, v_ringInst_x3f_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(lean_object* v_u_1126_, lean_object* v_type_1127_, lean_object* v_ringInst_x3f_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_u_1126_, v_type_1127_, v_ringInst_x3f_1128_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___boxed(lean_object* v_u_1141_, lean_object* v_type_1142_, lean_object* v_ringInst_x3f_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f(v_u_1141_, v_type_1142_, v_ringInst_x3f_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(lean_object* v_u_1163_, lean_object* v_type_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__1));
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v_u_1163_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
lean_inc_ref(v___x_1178_);
v___x_1179_ = l_Lean_mkConst(v___x_1176_, v___x_1178_);
lean_inc_ref(v_type_1164_);
v___x_1180_ = l_Lean_Expr_app___override(v___x_1179_, v_type_1164_);
v___x_1181_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1180_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1263_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1263_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1263_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
if (lean_obj_tag(v_a_1182_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1258_; 
lean_del_object(v___x_1184_);
v_val_1186_ = lean_ctor_get(v_a_1182_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1188_ = v_a_1182_;
v_isShared_1189_ = v_isSharedCheck_1258_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_val_1186_);
lean_dec(v_a_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1258_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___closed__3));
v___x_1191_ = l_Lean_mkConst(v___x_1190_, v___x_1178_);
lean_inc_ref(v_type_1164_);
v___x_1192_ = l_Lean_mkAppB(v___x_1191_, v_type_1164_, v_val_1186_);
v___x_1193_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_1192_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1249_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1249_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1249_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = l_Lean_Meta_mkNumeral(v_type_1164_, v___x_1205_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_a_1207_, 2);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v_a_1194_);
v___x_1208_ = l_Lean_Meta_isDefEqD(v_a_1194_, v_a_1207_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; uint8_t v___x_1210_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = lean_unbox(v_a_1209_);
lean_dec(v_a_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v_a_1212_; lean_object* v___x_1213_; 
lean_inc(v_a_1194_);
v___x_1211_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_a_1194_, v_a_1207_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1169_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; uint8_t v_verbose_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_verbose_1215_ = lean_ctor_get_uint8(v_a_1214_, 0);
lean_dec(v_a_1214_);
if (v_verbose_1215_ == 0)
{
lean_dec(v_a_1212_);
goto v___jp_1198_;
}
else
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Meta_Sym_reportIssue(v_a_1212_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_dec_ref_known(v___x_1216_, 1);
goto v___jp_1198_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
lean_del_object(v___x_1188_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1212_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
lean_del_object(v___x_1188_);
v_a_1225_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1213_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
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
lean_dec(v_a_1207_);
goto v___jp_1198_;
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1207_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
lean_del_object(v___x_1188_);
v_a_1233_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1208_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1208_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
lean_del_object(v___x_1188_);
v_a_1241_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1206_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1206_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
v___jp_1198_:
{
lean_object* v___x_1200_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_a_1194_);
v___x_1200_ = v___x_1188_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1194_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1200_);
v___x_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_del_object(v___x_1188_);
lean_dec_ref(v_type_1164_);
v_a_1250_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1193_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1193_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
lean_dec(v_a_1182_);
lean_dec_ref_known(v___x_1178_, 2);
lean_dec_ref(v_type_1164_);
v___x_1259_ = lean_box(0);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1259_);
v___x_1261_ = v___x_1184_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1178_, 2);
lean_dec_ref(v_type_1164_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f___boxed(lean_object* v_u_1264_, lean_object* v_type_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_u_1264_, v_type_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec(v_a_1266_);
return v_res_1277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__2));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(lean_object* v_u_1286_, lean_object* v_type_1287_, lean_object* v_semiringInst_x3f_1288_, lean_object* v_leInst_x3f_1289_, lean_object* v_ltInst_x3f_1290_, lean_object* v_preorderInst_x3f_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
if (lean_obj_tag(v_semiringInst_x3f_1288_) == 1)
{
if (lean_obj_tag(v_leInst_x3f_1289_) == 1)
{
if (lean_obj_tag(v_ltInst_x3f_1290_) == 1)
{
if (lean_obj_tag(v_preorderInst_x3f_1291_) == 1)
{
lean_object* v_val_1302_; lean_object* v_val_1303_; lean_object* v_val_1304_; lean_object* v_val_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_isOrdType_1310_; lean_object* v___x_1311_; 
v_val_1302_ = lean_ctor_get(v_semiringInst_x3f_1288_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_semiringInst_x3f_1288_, 1);
v_val_1303_ = lean_ctor_get(v_leInst_x3f_1289_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_leInst_x3f_1289_, 1);
v_val_1304_ = lean_ctor_get(v_ltInst_x3f_1290_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v_ltInst_x3f_1290_, 1);
v_val_1305_ = lean_ctor_get(v_preorderInst_x3f_1291_, 0);
lean_inc(v_val_1305_);
lean_dec_ref_known(v_preorderInst_x3f_1291_, 1);
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_u_1286_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_mkConst(v___x_1306_, v___x_1308_);
v_isOrdType_1310_ = l_Lean_mkApp5(v___x_1309_, v_type_1287_, v_val_1302_, v_val_1303_, v_val_1304_, v_val_1305_);
lean_inc_ref(v_isOrdType_1310_);
v___x_1311_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_isOrdType_1310_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
if (lean_obj_tag(v_a_1312_) == 1)
{
lean_dec_ref(v_isOrdType_1310_);
return v___x_1311_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___closed__3);
v___x_1314_ = l_Lean_indentExpr(v_isOrdType_1310_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1292_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; uint8_t v_verbose_1318_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v_verbose_1318_ = lean_ctor_get_uint8(v_a_1317_, 0);
lean_dec(v_a_1317_);
if (v_verbose_1318_ == 0)
{
lean_dec_ref_known(v___x_1315_, 2);
goto v___jp_1299_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_Sym_reportIssue(v___x_1315_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref_known(v___x_1319_, 1);
goto v___jp_1299_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref_known(v___x_1315_, 2);
v_a_1328_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1316_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1316_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_dec_ref(v_isOrdType_1310_);
return v___x_1311_;
}
}
else
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref_known(v_leInst_x3f_1289_, 1);
lean_dec_ref_known(v_semiringInst_x3f_1288_, 1);
lean_dec(v_preorderInst_x3f_1291_);
lean_dec_ref(v_type_1287_);
lean_dec(v_u_1286_);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_ltInst_x3f_1290_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_ltInst_x3f_1290_, 0);
lean_dec(v_unused_1344_);
v___x_1337_ = v_ltInst_x3f_1290_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v_ltInst_x3f_1290_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(0);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref_known(v_semiringInst_x3f_1288_, 1);
lean_dec(v_preorderInst_x3f_1291_);
lean_dec(v_ltInst_x3f_1290_);
lean_dec_ref(v_type_1287_);
lean_dec(v_u_1286_);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_leInst_x3f_1289_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_leInst_x3f_1289_, 0);
lean_dec(v_unused_1353_);
v___x_1346_ = v_leInst_x3f_1289_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v_leInst_x3f_1289_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_box(0);
if (v_isShared_1347_ == 0)
{
lean_ctor_set_tag(v___x_1346_, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_preorderInst_x3f_1291_);
lean_dec(v_ltInst_x3f_1290_);
lean_dec(v_leInst_x3f_1289_);
lean_dec_ref(v_type_1287_);
lean_dec(v_u_1286_);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_semiringInst_x3f_1288_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_semiringInst_x3f_1288_, 0);
lean_dec(v_unused_1362_);
v___x_1355_ = v_semiringInst_x3f_1288_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_semiringInst_x3f_1288_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_box(0);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v_preorderInst_x3f_1291_);
lean_dec(v_ltInst_x3f_1290_);
lean_dec(v_leInst_x3f_1289_);
lean_dec(v_semiringInst_x3f_1288_);
lean_dec_ref(v_type_1287_);
lean_dec(v_u_1286_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
v___jp_1299_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_1365_, lean_object* v_type_1366_, lean_object* v_semiringInst_x3f_1367_, lean_object* v_leInst_x3f_1368_, lean_object* v_ltInst_x3f_1369_, lean_object* v_preorderInst_x3f_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1365_, v_type_1366_, v_semiringInst_x3f_1367_, v_leInst_x3f_1368_, v_ltInst_x3f_1369_, v_preorderInst_x3f_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(lean_object* v_u_1379_, lean_object* v_type_1380_, lean_object* v_semiringInst_x3f_1381_, lean_object* v_leInst_x3f_1382_, lean_object* v_ltInst_x3f_1383_, lean_object* v_preorderInst_x3f_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_u_1379_, v_type_1380_, v_semiringInst_x3f_1381_, v_leInst_x3f_1382_, v_ltInst_x3f_1383_, v_preorderInst_x3f_1384_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___boxed(lean_object** _args){
lean_object* v_u_1397_ = _args[0];
lean_object* v_type_1398_ = _args[1];
lean_object* v_semiringInst_x3f_1399_ = _args[2];
lean_object* v_leInst_x3f_1400_ = _args[3];
lean_object* v_ltInst_x3f_1401_ = _args[4];
lean_object* v_preorderInst_x3f_1402_ = _args[5];
lean_object* v_a_1403_ = _args[6];
lean_object* v_a_1404_ = _args[7];
lean_object* v_a_1405_ = _args[8];
lean_object* v_a_1406_ = _args[9];
lean_object* v_a_1407_ = _args[10];
lean_object* v_a_1408_ = _args[11];
lean_object* v_a_1409_ = _args[12];
lean_object* v_a_1410_ = _args[13];
lean_object* v_a_1411_ = _args[14];
lean_object* v_a_1412_ = _args[15];
lean_object* v_a_1413_ = _args[16];
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f(v_u_1397_, v_type_1398_, v_semiringInst_x3f_1399_, v_leInst_x3f_1400_, v_ltInst_x3f_1401_, v_preorderInst_x3f_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec(v_a_1403_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(lean_object* v_u_1425_, lean_object* v_type_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_natModuleType_1437_; lean_object* v___x_1438_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_u_1425_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc_ref(v___x_1435_);
v___x_1436_ = l_Lean_mkConst(v___x_1433_, v___x_1435_);
lean_inc_ref(v_type_1426_);
v_natModuleType_1437_ = l_Lean_Expr_app___override(v___x_1436_, v_type_1426_);
v___x_1438_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_natModuleType_1437_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1452_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1452_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1452_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_a_1439_) == 1)
{
lean_object* v_val_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_del_object(v___x_1441_);
v_val_1443_ = lean_ctor_get(v_a_1439_, 0);
lean_inc(v_val_1443_);
lean_dec_ref_known(v_a_1439_, 1);
v___x_1444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
v___x_1445_ = l_Lean_mkConst(v___x_1444_, v___x_1435_);
v___x_1446_ = l_Lean_mkAppB(v___x_1445_, v_type_1426_, v_val_1443_);
v___x_1447_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1446_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_dec(v_a_1439_);
lean_dec_ref_known(v___x_1435_, 2);
lean_dec_ref(v_type_1426_);
v___x_1448_ = lean_box(0);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1448_);
v___x_1450_ = v___x_1441_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1435_, 2);
lean_dec_ref(v_type_1426_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___boxed(lean_object* v_u_1453_, lean_object* v_type_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1453_, v_type_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(lean_object* v_u_1462_, lean_object* v_type_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_u_1462_, v_type_1463_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___boxed(lean_object* v_u_1476_, lean_object* v_type_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f(v_u_1476_, v_type_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec(v_a_1478_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(lean_object* v_declName_1490_, lean_object* v_u_1491_, lean_object* v_type_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_u_1491_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_mkConst(v_declName_1490_, v___x_1500_);
v___x_1502_ = l_Lean_Expr_app___override(v___x_1501_, v_type_1492_);
v___x_1503_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1502_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg___boxed(lean_object* v_declName_1504_, lean_object* v_u_1505_, lean_object* v_type_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1504_, v_u_1505_, v_type_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(lean_object* v_declName_1514_, lean_object* v_u_1515_, lean_object* v_type_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v_declName_1514_, v_u_1515_, v_type_1516_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___boxed(lean_object* v_declName_1529_, lean_object* v_u_1530_, lean_object* v_type_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f(v_declName_1529_, v_u_1530_, v_type_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec(v_a_1532_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(lean_object* v_declName_1544_, lean_object* v_u_1545_, lean_object* v_type_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_u_1545_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_mkConst(v_declName_1544_, v___x_1555_);
v___x_1557_ = l_Lean_Expr_app___override(v___x_1556_, v_type_1546_);
v___x_1558_ = l_Lean_Meta_Sym_synthInstance(v___x_1557_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg___boxed(lean_object* v_declName_1559_, lean_object* v_u_1560_, lean_object* v_type_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1559_, v_u_1560_, v_type_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(lean_object* v_declName_1570_, lean_object* v_u_1571_, lean_object* v_type_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v_declName_1570_, v_u_1571_, v_type_1572_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___boxed(lean_object* v_declName_1585_, lean_object* v_u_1586_, lean_object* v_type_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst(v_declName_1585_, v_u_1586_, v_type_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec(v_a_1588_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(lean_object* v_declName_1600_, lean_object* v_u_1601_, lean_object* v_type_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1610_ = lean_box(0);
lean_inc_n(v_u_1601_, 2);
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_u_1601_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v_u_1601_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_u_1601_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_mkConst(v_declName_1600_, v___x_1613_);
lean_inc_ref_n(v_type_1602_, 2);
v___x_1615_ = l_Lean_mkApp3(v___x_1614_, v_type_1602_, v_type_1602_, v_type_1602_);
v___x_1616_ = l_Lean_Meta_Sym_synthInstance(v___x_1615_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg___boxed(lean_object* v_declName_1617_, lean_object* v_u_1618_, lean_object* v_type_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1617_, v_u_1618_, v_type_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(lean_object* v_declName_1628_, lean_object* v_u_1629_, lean_object* v_type_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v_declName_1628_, v_u_1629_, v_type_1630_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___boxed(lean_object* v_declName_1643_, lean_object* v_u_1644_, lean_object* v_type_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst(v_declName_1643_, v_u_1644_, v_type_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec(v_a_1646_);
return v_res_1657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = l_Lean_Level_ofNat(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(lean_object* v_u_1663_, lean_object* v_type_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1674_ = lean_box(0);
lean_inc(v_u_1663_);
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_u_1663_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_u_1663_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1673_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_mkConst(v___x_1672_, v___x_1677_);
v___x_1679_ = l_Lean_Int_mkType;
lean_inc_ref(v_type_1664_);
v___x_1680_ = l_Lean_mkApp3(v___x_1678_, v___x_1679_, v_type_1664_, v_type_1664_);
v___x_1681_ = l_Lean_Meta_Sym_synthInstance(v___x_1680_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___boxed(lean_object* v_u_1682_, lean_object* v_type_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1682_, v_type_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(lean_object* v_u_1692_, lean_object* v_type_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_u_1692_, v_type_1693_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___boxed(lean_object* v_u_1706_, lean_object* v_type_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst(v_u_1706_, v_type_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec(v_a_1708_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(lean_object* v_u_1720_, lean_object* v_type_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_1730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1731_ = lean_box(0);
lean_inc(v_u_1720_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_u_1720_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_u_1720_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1730_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_mkConst(v___x_1729_, v___x_1734_);
v___x_1736_ = l_Lean_Nat_mkType;
lean_inc_ref(v_type_1721_);
v___x_1737_ = l_Lean_mkApp3(v___x_1735_, v___x_1736_, v_type_1721_, v_type_1721_);
v___x_1738_ = l_Lean_Meta_Sym_synthInstance(v___x_1737_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg___boxed(lean_object* v_u_1739_, lean_object* v_type_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1739_, v_type_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(lean_object* v_u_1749_, lean_object* v_type_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_u_1749_, v_type_1750_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___boxed(lean_object* v_u_1763_, lean_object* v_type_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst(v_u_1763_, v_type_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec(v_a_1765_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(lean_object* v_leInst_x3f_1777_, lean_object* v_parentInst_x3f_1778_, lean_object* v_childInst_x3f_1779_, lean_object* v_toFieldName_1780_, lean_object* v_u_1781_, lean_object* v_type_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
if (lean_obj_tag(v_leInst_x3f_1777_) == 1)
{
if (lean_obj_tag(v_parentInst_x3f_1778_) == 1)
{
if (lean_obj_tag(v_childInst_x3f_1779_) == 1)
{
lean_object* v_val_1793_; lean_object* v_val_1794_; lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_toField_1799_; lean_object* v___x_1800_; 
v_val_1793_ = lean_ctor_get(v_leInst_x3f_1777_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v_leInst_x3f_1777_, 1);
v_val_1794_ = lean_ctor_get(v_parentInst_x3f_1778_, 0);
lean_inc_n(v_val_1794_, 2);
lean_dec_ref_known(v_parentInst_x3f_1778_, 1);
v_val_1795_ = lean_ctor_get(v_childInst_x3f_1779_, 0);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_u_1781_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_mkConst(v_toFieldName_1780_, v___x_1797_);
lean_inc(v_val_1795_);
v_toField_1799_ = l_Lean_mkApp3(v___x_1798_, v_type_1782_, v_val_1793_, v_val_1795_);
lean_inc_ref(v_toField_1799_);
v___x_1800_ = l_Lean_Meta_isDefEqD(v_val_1794_, v_toField_1799_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1831_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1831_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1831_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v_a_1807_; lean_object* v___x_1808_; 
lean_del_object(v___x_1803_);
lean_dec_ref_known(v_childInst_x3f_1779_, 1);
v___x_1806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkExpectedDefEqMsg___redArg(v_val_1794_, v_toField_1799_);
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1783_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; uint8_t v_verbose_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v_verbose_1810_ = lean_ctor_get_uint8(v_a_1809_, 0);
lean_dec(v_a_1809_);
if (v_verbose_1810_ == 0)
{
lean_dec(v_a_1807_);
goto v___jp_1790_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Meta_Sym_reportIssue(v_a_1807_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref_known(v___x_1811_, 1);
goto v___jp_1790_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1807_);
v_a_1820_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1808_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1808_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v___x_1829_; 
lean_dec_ref(v_toField_1799_);
lean_dec(v_val_1794_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_childInst_x3f_1779_);
v___x_1829_ = v___x_1803_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_childInst_x3f_1779_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_toField_1799_);
lean_dec(v_val_1794_);
lean_dec_ref_known(v_childInst_x3f_1779_, 1);
v_a_1832_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1800_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1800_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref_known(v_leInst_x3f_1777_, 1);
lean_dec_ref(v_type_1782_);
lean_dec(v_u_1781_);
lean_dec(v_toFieldName_1780_);
lean_dec(v_childInst_x3f_1779_);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_parentInst_x3f_1778_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_parentInst_x3f_1778_, 0);
lean_dec(v_unused_1848_);
v___x_1841_ = v_parentInst_x3f_1778_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v_parentInst_x3f_1778_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v_type_1782_);
lean_dec(v_u_1781_);
lean_dec(v_toFieldName_1780_);
lean_dec(v_childInst_x3f_1779_);
lean_dec(v_parentInst_x3f_1778_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_leInst_x3f_1777_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_leInst_x3f_1777_, 0);
lean_dec(v_unused_1857_);
v___x_1850_ = v_leInst_x3f_1777_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_leInst_x3f_1777_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_type_1782_);
lean_dec(v_u_1781_);
lean_dec(v_toFieldName_1780_);
lean_dec(v_childInst_x3f_1779_);
lean_dec(v_parentInst_x3f_1778_);
lean_dec(v_leInst_x3f_1777_);
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
v___jp_1790_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg___boxed(lean_object* v_leInst_x3f_1860_, lean_object* v_parentInst_x3f_1861_, lean_object* v_childInst_x3f_1862_, lean_object* v_toFieldName_1863_, lean_object* v_u_1864_, lean_object* v_type_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1860_, v_parentInst_x3f_1861_, v_childInst_x3f_1862_, v_toFieldName_1863_, v_u_1864_, v_type_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(lean_object* v_leInst_x3f_1874_, lean_object* v_parentInst_x3f_1875_, lean_object* v_childInst_x3f_1876_, lean_object* v_toFieldName_1877_, lean_object* v_u_1878_, lean_object* v_type_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_leInst_x3f_1874_, v_parentInst_x3f_1875_, v_childInst_x3f_1876_, v_toFieldName_1877_, v_u_1878_, v_type_1879_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___boxed(lean_object** _args){
lean_object* v_leInst_x3f_1892_ = _args[0];
lean_object* v_parentInst_x3f_1893_ = _args[1];
lean_object* v_childInst_x3f_1894_ = _args[2];
lean_object* v_toFieldName_1895_ = _args[3];
lean_object* v_u_1896_ = _args[4];
lean_object* v_type_1897_ = _args[5];
lean_object* v_a_1898_ = _args[6];
lean_object* v_a_1899_ = _args[7];
lean_object* v_a_1900_ = _args[8];
lean_object* v_a_1901_ = _args[9];
lean_object* v_a_1902_ = _args[10];
lean_object* v_a_1903_ = _args[11];
lean_object* v_a_1904_ = _args[12];
lean_object* v_a_1905_ = _args[13];
lean_object* v_a_1906_ = _args[14];
lean_object* v_a_1907_ = _args[15];
lean_object* v_a_1908_ = _args[16];
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f(v_leInst_x3f_1892_, v_parentInst_x3f_1893_, v_childInst_x3f_1894_, v_toFieldName_1895_, v_u_1896_, v_type_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec(v_a_1898_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(lean_object* v_parentInst_1910_, lean_object* v_inst_1911_, lean_object* v_toFieldName_1912_, lean_object* v_u_1913_, lean_object* v_type_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_toField_1923_; lean_object* v___x_1924_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_u_1913_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_mkConst(v_toFieldName_1912_, v___x_1921_);
v_toField_1923_ = l_Lean_mkAppB(v___x_1922_, v_type_1914_, v_inst_1911_);
v___x_1924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1910_, v_toField_1923_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg___boxed(lean_object* v_parentInst_1925_, lean_object* v_inst_1926_, lean_object* v_toFieldName_1927_, lean_object* v_u_1928_, lean_object* v_type_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1925_, v_inst_1926_, v_toFieldName_1927_, v_u_1928_, v_type_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(lean_object* v_parentInst_1936_, lean_object* v_inst_1937_, lean_object* v_toFieldName_1938_, lean_object* v_u_1939_, lean_object* v_type_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_parentInst_1936_, v_inst_1937_, v_toFieldName_1938_, v_u_1939_, v_type_1940_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___boxed(lean_object* v_parentInst_1953_, lean_object* v_inst_1954_, lean_object* v_toFieldName_1955_, lean_object* v_u_1956_, lean_object* v_type_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq(v_parentInst_1953_, v_inst_1954_, v_toFieldName_1955_, v_u_1956_, v_type_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
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
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(lean_object* v_parentInst_1970_, lean_object* v_inst_1971_, lean_object* v_toFieldName_1972_, lean_object* v_toHeteroName_1973_, lean_object* v_u_1974_, lean_object* v_type_1975_, lean_object* v_extraType_x3f_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_toField_1985_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_u_1974_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_inc_ref(v___x_1983_);
v___x_1984_ = l_Lean_mkConst(v_toFieldName_1972_, v___x_1983_);
lean_inc_ref(v_type_1975_);
v_toField_1985_ = l_Lean_mkAppB(v___x_1984_, v_type_1975_, v_inst_1971_);
if (lean_obj_tag(v_extraType_x3f_1976_) == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = l_Lean_mkConst(v_toHeteroName_1973_, v___x_1983_);
v___x_1987_ = l_Lean_mkAppB(v___x_1986_, v_type_1975_, v_toField_1985_);
v___x_1988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1970_, v___x_1987_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
return v___x_1988_;
}
else
{
lean_object* v_val_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_val_1989_ = lean_ctor_get(v_extraType_x3f_1976_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v_extraType_x3f_1976_, 1);
v___x_1990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1983_);
v___x_1992_ = l_Lean_mkConst(v_toHeteroName_1973_, v___x_1991_);
v___x_1993_ = l_Lean_mkApp3(v___x_1992_, v_val_1989_, v_type_1975_, v_toField_1985_);
v___x_1994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_parentInst_1970_, v___x_1993_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg___boxed(lean_object* v_parentInst_1995_, lean_object* v_inst_1996_, lean_object* v_toFieldName_1997_, lean_object* v_toHeteroName_1998_, lean_object* v_u_1999_, lean_object* v_type_2000_, lean_object* v_extraType_x3f_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_1995_, v_inst_1996_, v_toFieldName_1997_, v_toHeteroName_1998_, v_u_1999_, v_type_2000_, v_extraType_x3f_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(lean_object* v_parentInst_2008_, lean_object* v_inst_2009_, lean_object* v_toFieldName_2010_, lean_object* v_toHeteroName_2011_, lean_object* v_u_2012_, lean_object* v_type_2013_, lean_object* v_extraType_x3f_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_parentInst_2008_, v_inst_2009_, v_toFieldName_2010_, v_toHeteroName_2011_, v_u_2012_, v_type_2013_, v_extraType_x3f_2014_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___boxed(lean_object** _args){
lean_object* v_parentInst_2027_ = _args[0];
lean_object* v_inst_2028_ = _args[1];
lean_object* v_toFieldName_2029_ = _args[2];
lean_object* v_toHeteroName_2030_ = _args[3];
lean_object* v_u_2031_ = _args[4];
lean_object* v_type_2032_ = _args[5];
lean_object* v_extraType_x3f_2033_ = _args[6];
lean_object* v_a_2034_ = _args[7];
lean_object* v_a_2035_ = _args[8];
lean_object* v_a_2036_ = _args[9];
lean_object* v_a_2037_ = _args[10];
lean_object* v_a_2038_ = _args[11];
lean_object* v_a_2039_ = _args[12];
lean_object* v_a_2040_ = _args[13];
lean_object* v_a_2041_ = _args[14];
lean_object* v_a_2042_ = _args[15];
lean_object* v_a_2043_ = _args[16];
lean_object* v_a_2044_ = _args[17];
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq(v_parentInst_2027_, v_inst_2028_, v_toFieldName_2029_, v_toHeteroName_2030_, v_u_2031_, v_type_2032_, v_extraType_x3f_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec(v_a_2034_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(lean_object* v_u_2050_, lean_object* v_type_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_smulType_2067_; lean_object* v___x_2068_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2061_ = lean_box(0);
lean_inc(v_u_2050_);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_u_2050_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_u_2050_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2060_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
lean_inc_ref(v___x_2064_);
v___x_2065_ = l_Lean_mkConst(v___x_2059_, v___x_2064_);
v___x_2066_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2051_, 2);
v_smulType_2067_ = l_Lean_mkApp3(v___x_2065_, v___x_2066_, v_type_2051_, v_type_2051_);
v___x_2068_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2067_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2105_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2105_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2105_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
if (lean_obj_tag(v_a_2069_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2100_; 
lean_del_object(v___x_2071_);
v_val_2073_ = lean_ctor_get(v_a_2069_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2069_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2075_ = v_a_2069_;
v_isShared_2076_ = v_isSharedCheck_2100_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_val_2073_);
lean_dec(v_a_2069_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2100_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2078_ = l_Lean_mkConst(v___x_2077_, v___x_2064_);
lean_inc_ref(v_type_2051_);
v___x_2079_ = l_Lean_mkApp4(v___x_2078_, v___x_2066_, v_type_2051_, v_type_2051_, v_val_2073_);
v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2079_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2091_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_a_2081_);
v___x_2086_ = v___x_2075_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_del_object(v___x_2075_);
v_a_2092_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2080_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2080_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_dec(v_a_2069_);
lean_dec_ref_known(v___x_2064_, 2);
lean_dec_ref(v_type_2051_);
v___x_2101_ = lean_box(0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2101_);
v___x_2103_ = v___x_2071_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2064_, 2);
lean_dec_ref(v_type_2051_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___boxed(lean_object* v_u_2106_, lean_object* v_type_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2106_, v_type_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(lean_object* v_u_2116_, lean_object* v_type_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_u_2116_, v_type_2117_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___boxed(lean_object* v_u_2130_, lean_object* v_type_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f(v_u_2130_, v_type_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec(v_a_2132_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(lean_object* v_u_2144_, lean_object* v_type_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_smulType_2161_; lean_object* v___x_2162_; 
v___x_2153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_2154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2155_ = lean_box(0);
lean_inc(v_u_2144_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_u_2144_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v_u_2144_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2154_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
lean_inc_ref(v___x_2158_);
v___x_2159_ = l_Lean_mkConst(v___x_2153_, v___x_2158_);
v___x_2160_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2145_, 2);
v_smulType_2161_ = l_Lean_mkApp3(v___x_2159_, v___x_2160_, v_type_2145_, v_type_2145_);
v___x_2162_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_smulType_2161_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2199_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2199_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2199_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
if (lean_obj_tag(v_a_2163_) == 1)
{
lean_object* v_val_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2194_; 
lean_del_object(v___x_2165_);
v_val_2167_ = lean_ctor_get(v_a_2163_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_a_2163_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2169_ = v_a_2163_;
v_isShared_2170_ = v_isSharedCheck_2194_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_val_2167_);
lean_dec(v_a_2163_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2194_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2172_ = l_Lean_mkConst(v___x_2171_, v___x_2158_);
lean_inc_ref(v_type_2145_);
v___x_2173_ = l_Lean_mkApp4(v___x_2172_, v___x_2160_, v_type_2145_, v_type_2145_, v_val_2167_);
v___x_2174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2173_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2185_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v_a_2175_);
v___x_2180_ = v___x_2169_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2180_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_del_object(v___x_2169_);
v_a_2186_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2174_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2174_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_dec(v_a_2163_);
lean_dec_ref_known(v___x_2158_, 2);
lean_dec_ref(v_type_2145_);
v___x_2195_ = lean_box(0);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2195_);
v___x_2197_ = v___x_2165_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2158_, 2);
lean_dec_ref(v_type_2145_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg___boxed(lean_object* v_u_2200_, lean_object* v_type_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2200_, v_type_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(lean_object* v_u_2210_, lean_object* v_type_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_u_2210_, v_type_2211_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___boxed(lean_object* v_u_2224_, lean_object* v_type_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f(v_u_2224_, v_type_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec(v_a_2226_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v_ks_2242_; lean_object* v_vs_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2269_; 
v_ks_2242_ = lean_ctor_get(v_x_2238_, 0);
v_vs_2243_ = lean_ctor_get(v_x_2238_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_x_2238_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2245_ = v_x_2238_;
v_isShared_2246_ = v_isSharedCheck_2269_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_vs_2243_);
lean_inc(v_ks_2242_);
lean_dec(v_x_2238_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2269_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_array_get_size(v_ks_2242_);
v___x_2248_ = lean_nat_dec_lt(v_x_2239_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
lean_dec(v_x_2239_);
v___x_2249_ = lean_array_push(v_ks_2242_, v_x_2240_);
v___x_2250_ = lean_array_push(v_vs_2243_, v_x_2241_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2250_);
lean_ctor_set(v___x_2245_, 0, v___x_2249_);
v___x_2252_ = v___x_2245_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
else
{
lean_object* v_k_x27_2254_; size_t v___x_2255_; size_t v___x_2256_; uint8_t v___x_2257_; 
v_k_x27_2254_ = lean_array_fget_borrowed(v_ks_2242_, v_x_2239_);
v___x_2255_ = lean_ptr_addr(v_x_2240_);
v___x_2256_ = lean_ptr_addr(v_k_x27_2254_);
v___x_2257_ = lean_usize_dec_eq(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2259_; 
if (v_isShared_2246_ == 0)
{
v___x_2259_ = v___x_2245_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_ks_2242_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_vs_2243_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_add(v_x_2239_, v___x_2260_);
lean_dec(v_x_2239_);
v_x_2238_ = v___x_2259_;
v_x_2239_ = v___x_2261_;
goto _start;
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2264_ = lean_array_fset(v_ks_2242_, v_x_2239_, v_x_2240_);
v___x_2265_ = lean_array_fset(v_vs_2243_, v_x_2239_, v_x_2241_);
lean_dec(v_x_2239_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2265_);
lean_ctor_set(v___x_2245_, 0, v___x_2264_);
v___x_2267_ = v___x_2245_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2270_, lean_object* v_k_2271_, lean_object* v_v_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2270_, v___x_2273_, v_k_2271_, v_v_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_2276_, size_t v_x_2277_, size_t v_x_2278_, lean_object* v_x_2279_, lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v_es_2281_; size_t v___x_2282_; size_t v___x_2283_; lean_object* v_j_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_es_2281_ = lean_ctor_get(v_x_2276_, 0);
v___x_2282_ = ((size_t)31ULL);
v___x_2283_ = lean_usize_land(v_x_2277_, v___x_2282_);
v_j_2284_ = lean_usize_to_nat(v___x_2283_);
v___x_2285_ = lean_array_get_size(v_es_2281_);
v___x_2286_ = lean_nat_dec_lt(v_j_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
lean_dec(v_j_2284_);
lean_dec(v_x_2280_);
lean_dec_ref(v_x_2279_);
return v_x_2276_;
}
else
{
lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2327_; 
lean_inc_ref(v_es_2281_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_x_2276_, 0);
lean_dec(v_unused_2328_);
v___x_2288_ = v_x_2276_;
v_isShared_2289_ = v_isSharedCheck_2327_;
goto v_resetjp_2287_;
}
else
{
lean_dec(v_x_2276_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2327_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_v_2290_; lean_object* v___x_2291_; lean_object* v_xs_x27_2292_; lean_object* v___y_2294_; 
v_v_2290_ = lean_array_fget(v_es_2281_, v_j_2284_);
v___x_2291_ = lean_box(0);
v_xs_x27_2292_ = lean_array_fset(v_es_2281_, v_j_2284_, v___x_2291_);
switch(lean_obj_tag(v_v_2290_))
{
case 0:
{
lean_object* v_key_2299_; lean_object* v_val_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2312_; 
v_key_2299_ = lean_ctor_get(v_v_2290_, 0);
v_val_2300_ = lean_ctor_get(v_v_2290_, 1);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_v_2290_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2302_ = v_v_2290_;
v_isShared_2303_ = v_isSharedCheck_2312_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_val_2300_);
lean_inc(v_key_2299_);
lean_dec(v_v_2290_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2312_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
size_t v___x_2304_; size_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2304_ = lean_ptr_addr(v_x_2279_);
v___x_2305_ = lean_ptr_addr(v_key_2299_);
v___x_2306_ = lean_usize_dec_eq(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_del_object(v___x_2302_);
v___x_2307_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2299_, v_val_2300_, v_x_2279_, v_x_2280_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___y_2294_ = v___x_2308_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2310_; 
lean_dec(v_val_2300_);
lean_dec(v_key_2299_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v_x_2280_);
lean_ctor_set(v___x_2302_, 0, v_x_2279_);
v___x_2310_ = v___x_2302_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_x_2279_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_x_2280_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
v___y_2294_ = v___x_2310_;
goto v___jp_2293_;
}
}
}
}
case 1:
{
lean_object* v_node_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2325_; 
v_node_2313_ = lean_ctor_get(v_v_2290_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_v_2290_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2315_ = v_v_2290_;
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_node_2313_);
lean_dec(v_v_2290_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2325_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2317_ = ((size_t)5ULL);
v___x_2318_ = lean_usize_shift_right(v_x_2277_, v___x_2317_);
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_add(v_x_2278_, v___x_2319_);
v___x_2321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_node_2313_, v___x_2318_, v___x_2320_, v_x_2279_, v_x_2280_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2321_);
v___x_2323_ = v___x_2315_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
v___y_2294_ = v___x_2323_;
goto v___jp_2293_;
}
}
}
default: 
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_x_2279_);
lean_ctor_set(v___x_2326_, 1, v_x_2280_);
v___y_2294_ = v___x_2326_;
goto v___jp_2293_;
}
}
v___jp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = lean_array_fset(v_xs_x27_2292_, v_j_2284_, v___y_2294_);
lean_dec(v_j_2284_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2295_);
v___x_2297_ = v___x_2288_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
lean_object* v_ks_2329_; lean_object* v_vs_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2348_; 
v_ks_2329_ = lean_ctor_get(v_x_2276_, 0);
v_vs_2330_ = lean_ctor_get(v_x_2276_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2332_ = v_x_2276_;
v_isShared_2333_ = v_isSharedCheck_2348_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_vs_2330_);
lean_inc(v_ks_2329_);
lean_dec(v_x_2276_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2348_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_ks_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_vs_2330_);
v___x_2335_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v_newNode_2336_; size_t v___x_2337_; uint8_t v___x_2338_; 
v_newNode_2336_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v___x_2335_, v_x_2279_, v_x_2280_);
v___x_2337_ = ((size_t)7ULL);
v___x_2338_ = lean_usize_dec_le(v___x_2337_, v_x_2278_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2339_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2336_);
v___x_2340_ = lean_unsigned_to_nat(4u);
v___x_2341_ = lean_nat_dec_lt(v___x_2339_, v___x_2340_);
lean_dec(v___x_2339_);
if (v___x_2341_ == 0)
{
lean_object* v_ks_2342_; lean_object* v_vs_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_ks_2342_ = lean_ctor_get(v_newNode_2336_, 0);
lean_inc_ref(v_ks_2342_);
v_vs_2343_ = lean_ctor_get(v_newNode_2336_, 1);
lean_inc_ref(v_vs_2343_);
lean_dec_ref(v_newNode_2336_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___closed__0);
v___x_2346_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_x_2278_, v_ks_2342_, v_vs_2343_, v___x_2344_, v___x_2345_);
lean_dec_ref(v_vs_2343_);
lean_dec_ref(v_ks_2342_);
return v___x_2346_;
}
else
{
return v_newNode_2336_;
}
}
else
{
return v_newNode_2336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(size_t v_depth_2349_, lean_object* v_keys_2350_, lean_object* v_vals_2351_, lean_object* v_i_2352_, lean_object* v_entries_2353_){
_start:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_array_get_size(v_keys_2350_);
v___x_2355_ = lean_nat_dec_lt(v_i_2352_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec(v_i_2352_);
return v_entries_2353_;
}
else
{
lean_object* v_k_2356_; lean_object* v_v_2357_; size_t v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; uint64_t v___x_2361_; size_t v_h_2362_; size_t v___x_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; size_t v___x_2367_; size_t v_h_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_k_2356_ = lean_array_fget_borrowed(v_keys_2350_, v_i_2352_);
v_v_2357_ = lean_array_fget_borrowed(v_vals_2351_, v_i_2352_);
v___x_2358_ = lean_ptr_addr(v_k_2356_);
v___x_2359_ = ((size_t)3ULL);
v___x_2360_ = lean_usize_shift_right(v___x_2358_, v___x_2359_);
v___x_2361_ = lean_usize_to_uint64(v___x_2360_);
v_h_2362_ = lean_uint64_to_usize(v___x_2361_);
v___x_2363_ = ((size_t)5ULL);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_sub(v_depth_2349_, v___x_2365_);
v___x_2367_ = lean_usize_mul(v___x_2363_, v___x_2366_);
v_h_2368_ = lean_usize_shift_right(v_h_2362_, v___x_2367_);
v___x_2369_ = lean_nat_add(v_i_2352_, v___x_2364_);
lean_dec(v_i_2352_);
lean_inc(v_v_2357_);
lean_inc(v_k_2356_);
v___x_2370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_entries_2353_, v_h_2368_, v_depth_2349_, v_k_2356_, v_v_2357_);
v_i_2352_ = v___x_2369_;
v_entries_2353_ = v___x_2370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_i_2375_, lean_object* v_entries_2376_){
_start:
{
size_t v_depth_boxed_2377_; lean_object* v_res_2378_; 
v_depth_boxed_2377_ = lean_unbox_usize(v_depth_2372_);
lean_dec(v_depth_2372_);
v_res_2378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2377_, v_keys_2373_, v_vals_2374_, v_i_2375_, v_entries_2376_);
lean_dec_ref(v_vals_2374_);
lean_dec_ref(v_keys_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
size_t v_x_527721__boxed_2384_; size_t v_x_527722__boxed_2385_; lean_object* v_res_2386_; 
v_x_527721__boxed_2384_ = lean_unbox_usize(v_x_2380_);
lean_dec(v_x_2380_);
v_x_527722__boxed_2385_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2379_, v_x_527721__boxed_2384_, v_x_527722__boxed_2385_, v_x_2382_, v_x_2383_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
size_t v___x_2390_; size_t v___x_2391_; size_t v___x_2392_; uint64_t v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2390_ = lean_ptr_addr(v_x_2388_);
v___x_2391_ = ((size_t)3ULL);
v___x_2392_ = lean_usize_shift_right(v___x_2390_, v___x_2391_);
v___x_2393_ = lean_usize_to_uint64(v___x_2392_);
v___x_2394_ = lean_uint64_to_usize(v___x_2393_);
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_2387_, v___x_2394_, v___x_2395_, v_x_2388_, v_x_2389_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0(lean_object* v_type_2397_, lean_object* v_s_2398_){
_start:
{
lean_object* v_structs_2399_; lean_object* v_typeIdOf_2400_; lean_object* v_exprToStructId_2401_; lean_object* v_exprToStructIdEntries_2402_; lean_object* v_forbiddenNatModules_2403_; lean_object* v_natStructs_2404_; lean_object* v_natTypeIdOf_2405_; lean_object* v_exprToNatStructId_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2415_; 
v_structs_2399_ = lean_ctor_get(v_s_2398_, 0);
v_typeIdOf_2400_ = lean_ctor_get(v_s_2398_, 1);
v_exprToStructId_2401_ = lean_ctor_get(v_s_2398_, 2);
v_exprToStructIdEntries_2402_ = lean_ctor_get(v_s_2398_, 3);
v_forbiddenNatModules_2403_ = lean_ctor_get(v_s_2398_, 4);
v_natStructs_2404_ = lean_ctor_get(v_s_2398_, 5);
v_natTypeIdOf_2405_ = lean_ctor_get(v_s_2398_, 6);
v_exprToNatStructId_2406_ = lean_ctor_get(v_s_2398_, 7);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_s_2398_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2408_ = v_s_2398_;
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_exprToNatStructId_2406_);
lean_inc(v_natTypeIdOf_2405_);
lean_inc(v_natStructs_2404_);
lean_inc(v_forbiddenNatModules_2403_);
lean_inc(v_exprToStructIdEntries_2402_);
lean_inc(v_exprToStructId_2401_);
lean_inc(v_typeIdOf_2400_);
lean_inc(v_structs_2399_);
lean_dec(v_s_2398_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2415_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2410_ = lean_box(0);
v___x_2411_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_forbiddenNatModules_2403_, v_type_2397_, v___x_2410_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 4, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_structs_2399_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_typeIdOf_2400_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_exprToStructId_2401_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_exprToStructIdEntries_2402_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2414_, 5, v_natStructs_2404_);
lean_ctor_set(v_reuseFailAlloc_2414_, 6, v_natTypeIdOf_2405_);
lean_ctor_set(v_reuseFailAlloc_2414_, 7, v_exprToNatStructId_2406_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(lean_object* v_a_2416_, lean_object* v_00___2417_){
_start:
{
if (lean_obj_tag(v_a_2416_) == 0)
{
uint8_t v___x_2418_; 
v___x_2418_ = 0;
return v___x_2418_;
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = 1;
return v___x_2419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2___boxed(lean_object* v_a_2420_, lean_object* v_00___2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2420_, v_00___2421_);
lean_dec(v_a_2420_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1(lean_object* v___x_2424_, lean_object* v_s_2425_){
_start:
{
lean_object* v_structs_2426_; lean_object* v_typeIdOf_2427_; lean_object* v_exprToStructId_2428_; lean_object* v_exprToStructIdEntries_2429_; lean_object* v_forbiddenNatModules_2430_; lean_object* v_natStructs_2431_; lean_object* v_natTypeIdOf_2432_; lean_object* v_exprToNatStructId_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
v_structs_2426_ = lean_ctor_get(v_s_2425_, 0);
v_typeIdOf_2427_ = lean_ctor_get(v_s_2425_, 1);
v_exprToStructId_2428_ = lean_ctor_get(v_s_2425_, 2);
v_exprToStructIdEntries_2429_ = lean_ctor_get(v_s_2425_, 3);
v_forbiddenNatModules_2430_ = lean_ctor_get(v_s_2425_, 4);
v_natStructs_2431_ = lean_ctor_get(v_s_2425_, 5);
v_natTypeIdOf_2432_ = lean_ctor_get(v_s_2425_, 6);
v_exprToNatStructId_2433_ = lean_ctor_get(v_s_2425_, 7);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_s_2425_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2435_ = v_s_2425_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_exprToNatStructId_2433_);
lean_inc(v_natTypeIdOf_2432_);
lean_inc(v_natStructs_2431_);
lean_inc(v_forbiddenNatModules_2430_);
lean_inc(v_exprToStructIdEntries_2429_);
lean_inc(v_exprToStructId_2428_);
lean_inc(v_typeIdOf_2427_);
lean_inc(v_structs_2426_);
lean_dec(v_s_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_array_push(v_structs_2426_, v___x_2424_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_typeIdOf_2427_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_exprToStructId_2428_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_exprToStructIdEntries_2429_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_forbiddenNatModules_2430_);
lean_ctor_set(v_reuseFailAlloc_2440_, 5, v_natStructs_2431_);
lean_ctor_set(v_reuseFailAlloc_2440_, 6, v_natTypeIdOf_2432_);
lean_ctor_set(v_reuseFailAlloc_2440_, 7, v_exprToNatStructId_2433_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_unsigned_to_nat(32u);
v___x_2449_ = lean_mk_empty_array_with_capacity(v___x_2448_);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5(void){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2451_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = l_Lean_mkRawNatLit(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = l_Lean_Int_mkType;
v___x_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = l_Lean_Nat_mkType;
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(lean_object* v_type_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___y_2575_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; uint8_t v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___f_2640_; lean_object* v___x_2641_; 
lean_inc_ref_n(v_type_2562_, 2);
v___f_2640_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2640_, 0, v_type_2562_);
v___x_2641_ = l_Lean_Meta_getDecLevel_x3f(v_type_2562_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_3558_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_3558_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_3558_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
if (lean_obj_tag(v_a_2642_) == 1)
{
lean_object* v_val_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_2644_);
v_val_2646_ = lean_ctor_get(v_a_2642_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_2642_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_2648_ = v_a_2642_;
v_isShared_2649_ = v_isSharedCheck_3553_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_val_2646_);
lean_dec(v_a_2642_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_3553_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; 
lean_inc_ref(v_type_2562_);
v___x_2650_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_type_2562_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_3552_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_3552_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_3552_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2655_, v_val_2646_, v_type_2562_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_2658_, v_val_2646_, v_type_2562_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_n(v_a_2660_, 2);
lean_dec_ref_known(v___x_2659_, 1);
lean_inc(v_a_2657_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2661_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2646_, v_type_2562_, v_a_2660_, v_a_2657_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_homomulFn_x3f_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v_ltFn_x3f_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; uint8_t v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_leFn_x3f_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; uint8_t v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v_charInst_x3f_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___x_3174_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
lean_inc(v_a_2657_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3174_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2646_, v_type_2562_, v_a_2657_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
lean_inc(v_a_2657_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3176_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2646_, v_type_2562_, v_a_2657_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
lean_inc(v_a_2657_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3178_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_val_2646_, v_type_2562_, v_a_2657_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; uint8_t v___y_3201_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; uint8_t v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___x_3385_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3385_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2565_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; uint8_t v___y_3388_; uint8_t v_ring_3473_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v_ring_3473_ = lean_ctor_get_uint8(v_a_3386_, sizeof(void*)*14 + 21);
lean_dec(v_a_3386_);
if (v_ring_3473_ == 0)
{
v___y_3388_ = v_ring_3473_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3474_ = lean_box(0);
v___x_3475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2651_, v___x_3474_);
if (v___x_3475_ == 0)
{
v___y_3388_ = v___x_3475_;
goto v___jp_3387_;
}
else
{
if (lean_obj_tag(v_a_3175_) == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v___x_3476_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3477_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3476_, v___f_2640_, v_a_2563_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3485_; 
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; 
v_unused_3486_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3486_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3481_ = lean_box(0);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3481_);
v___x_3483_ = v___x_3479_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
v_a_3487_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3477_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3477_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = 0;
v___y_3388_ = v___x_3495_;
goto v___jp_3387_;
}
}
}
v___jp_3387_:
{
lean_object* v___x_3389_; 
lean_inc(v_a_2651_);
v___x_3389_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getCommRingInst_x3f(v_a_2651_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_n(v_a_3390_, 2);
lean_dec_ref_known(v___x_3389_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg(v_val_2646_, v_type_2562_, v_a_3390_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc_n(v_a_3392_, 2);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3393_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg(v_val_2646_, v_type_2562_, v_a_3392_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3448_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3448_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3448_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 1)
{
lean_object* v_val_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_del_object(v___x_3396_);
v_val_3398_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v_a_3394_, 1);
v___x_3399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_3399_, v_val_2646_, v_type_2562_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc_n(v_a_3401_, 2);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
v___x_3403_ = lean_box(0);
lean_inc_n(v_val_2646_, 3);
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_val_2646_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
lean_inc_ref(v___x_3404_);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_val_2646_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
lean_inc_ref(v___x_3405_);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_val_2646_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
lean_inc_ref(v___x_3406_);
v___x_3407_ = l_Lean_mkConst(v___x_3402_, v___x_3406_);
lean_inc_ref_n(v_type_2562_, 3);
v___x_3408_ = l_Lean_mkApp4(v___x_3407_, v_type_2562_, v_type_2562_, v_type_2562_, v_a_3401_);
v___x_3409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3408_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3409_) == 0)
{
if (lean_obj_tag(v_a_2657_) == 1)
{
if (lean_obj_tag(v_a_3175_) == 1)
{
lean_object* v_a_3410_; lean_object* v_val_3411_; lean_object* v_val_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3409_, 1);
v_val_3411_ = lean_ctor_get(v_a_2657_, 0);
v_val_3412_ = lean_ctor_get(v_a_3175_, 0);
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_3404_);
v___x_3414_ = l_Lean_mkConst(v___x_3413_, v___x_3404_);
lean_inc(v_val_3412_);
lean_inc(v_val_3411_);
lean_inc(v_a_3401_);
lean_inc_ref(v_type_2562_);
v___x_3415_ = l_Lean_mkApp4(v___x_3414_, v_type_2562_, v_a_3401_, v_val_3411_, v_val_3412_);
v___x_3416_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_3415_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
if (lean_obj_tag(v_a_3417_) == 0)
{
lean_dec_ref_known(v_a_3175_, 1);
v___y_3343_ = v_a_2563_;
v___y_3344_ = v___x_3404_;
v___y_3345_ = v_a_2568_;
v___y_3346_ = v_a_3417_;
v___y_3347_ = v_a_2565_;
v___y_3348_ = v_a_2566_;
v___y_3349_ = v_a_2572_;
v___y_3350_ = v___x_3406_;
v___y_3351_ = v___y_3388_;
v___y_3352_ = v_a_3410_;
v___y_3353_ = v_a_2569_;
v___y_3354_ = v_a_2570_;
v___y_3355_ = v_a_2571_;
v___y_3356_ = v_a_2564_;
v___y_3357_ = v_a_3390_;
v___y_3358_ = v___x_3405_;
v___y_3359_ = v_val_3398_;
v___y_3360_ = v_a_3392_;
v___y_3361_ = v_a_2567_;
v___y_3362_ = v_a_3401_;
goto v___jp_3342_;
}
else
{
if (v___y_3388_ == 0)
{
v___y_3289_ = v_a_2563_;
v___y_3290_ = v___x_3404_;
v___y_3291_ = v_a_2568_;
v___y_3292_ = v_a_3417_;
v___y_3293_ = v_a_2565_;
v___y_3294_ = v_a_2566_;
v___y_3295_ = v_a_2572_;
v___y_3296_ = v___x_3406_;
v___y_3297_ = v___y_3388_;
v___y_3298_ = v_a_3410_;
v___y_3299_ = v_a_2569_;
v___y_3300_ = v_a_2570_;
v___y_3301_ = v_a_2571_;
v___y_3302_ = v_a_2564_;
v___y_3303_ = v_a_3390_;
v___y_3304_ = v___x_3405_;
v___y_3305_ = v_a_3392_;
v___y_3306_ = v_val_3398_;
v___y_3307_ = v_a_2567_;
v___y_3308_ = v_a_3401_;
v___y_3309_ = v_a_3175_;
goto v___jp_3288_;
}
else
{
lean_dec_ref_known(v_a_3175_, 1);
v___y_3343_ = v_a_2563_;
v___y_3344_ = v___x_3404_;
v___y_3345_ = v_a_2568_;
v___y_3346_ = v_a_3417_;
v___y_3347_ = v_a_2565_;
v___y_3348_ = v_a_2566_;
v___y_3349_ = v_a_2572_;
v___y_3350_ = v___x_3406_;
v___y_3351_ = v___y_3388_;
v___y_3352_ = v_a_3410_;
v___y_3353_ = v_a_2569_;
v___y_3354_ = v_a_2570_;
v___y_3355_ = v_a_2571_;
v___y_3356_ = v_a_2564_;
v___y_3357_ = v_a_3390_;
v___y_3358_ = v___x_3405_;
v___y_3359_ = v_val_3398_;
v___y_3360_ = v_a_3392_;
v___y_3361_ = v_a_2567_;
v___y_3362_ = v_a_3401_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3410_);
lean_dec_ref_known(v_a_3175_, 1);
lean_dec_ref_known(v_a_2657_, 1);
lean_dec_ref_known(v___x_3406_, 2);
lean_dec_ref_known(v___x_3405_, 2);
lean_dec_ref_known(v___x_3404_, 2);
lean_dec(v_a_3401_);
lean_dec(v_val_3398_);
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3418_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3416_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3416_);
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
lean_object* v_a_3426_; 
lean_dec(v_a_3175_);
v_a_3426_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3365_ = v___y_3388_;
v___y_3366_ = v_a_3426_;
v___y_3367_ = v___x_3404_;
v___y_3368_ = v_a_3390_;
v___y_3369_ = v___x_3405_;
v___y_3370_ = v_a_3392_;
v___y_3371_ = v_val_3398_;
v___y_3372_ = v___x_3406_;
v___y_3373_ = v_a_3401_;
v___y_3374_ = v_a_2563_;
v___y_3375_ = v_a_2564_;
v___y_3376_ = v_a_2565_;
v___y_3377_ = v_a_2566_;
v___y_3378_ = v_a_2567_;
v___y_3379_ = v_a_2568_;
v___y_3380_ = v_a_2569_;
v___y_3381_ = v_a_2570_;
v___y_3382_ = v_a_2571_;
v___y_3383_ = v_a_2572_;
goto v___jp_3364_;
}
}
else
{
lean_object* v_a_3427_; 
lean_dec(v_a_3175_);
v_a_3427_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3365_ = v___y_3388_;
v___y_3366_ = v_a_3427_;
v___y_3367_ = v___x_3404_;
v___y_3368_ = v_a_3390_;
v___y_3369_ = v___x_3405_;
v___y_3370_ = v_a_3392_;
v___y_3371_ = v_val_3398_;
v___y_3372_ = v___x_3406_;
v___y_3373_ = v_a_3401_;
v___y_3374_ = v_a_2563_;
v___y_3375_ = v_a_2564_;
v___y_3376_ = v_a_2565_;
v___y_3377_ = v_a_2566_;
v___y_3378_ = v_a_2567_;
v___y_3379_ = v_a_2568_;
v___y_3380_ = v_a_2569_;
v___y_3381_ = v_a_2570_;
v___y_3382_ = v_a_2571_;
v___y_3383_ = v_a_2572_;
goto v___jp_3364_;
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec_ref_known(v___x_3406_, 2);
lean_dec_ref_known(v___x_3405_, 2);
lean_dec_ref_known(v___x_3404_, 2);
lean_dec(v_a_3401_);
lean_dec(v_val_3398_);
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3428_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3409_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3409_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_val_3398_);
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3436_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3400_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3400_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_dec(v_a_3394_);
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v___x_3444_ = lean_box(0);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3444_);
v___x_3446_ = v___x_3396_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_a_3392_);
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3449_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3393_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3393_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_a_3390_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3457_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3391_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3391_);
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
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3465_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3389_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3389_);
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
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3496_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3385_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3385_);
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
v___jp_3180_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__50));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc(v___y_3185_);
lean_inc(v_a_2657_);
v___x_3203_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2657_, v___y_3185_, v_a_3177_, v___x_3202_, v_val_2646_, v_type_2562_, v___y_3199_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__53));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc(v_a_2657_);
v___x_3206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_checkToFieldDefEq_x3f___redArg(v_a_2657_, v_a_3204_, v_a_3179_, v___x_3205_, v_val_2646_, v_type_2562_, v___y_3199_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3206_, 1);
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__0));
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkRingInst_x3f___redArg___closed__1));
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__2));
v___x_3211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
lean_inc_n(v___y_3182_, 2);
v___x_3212_ = l_Lean_mkConst(v___x_3211_, v___y_3182_);
lean_inc_ref(v___y_3197_);
lean_inc_ref_n(v_type_2562_, 3);
v___x_3213_ = l_Lean_mkAppB(v___x_3212_, v_type_2562_, v___y_3197_);
v___x_3214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__56));
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_3216_ = l_Lean_mkConst(v___x_3215_, v___y_3182_);
lean_inc_ref(v___x_3213_);
v___x_3217_ = l_Lean_mkAppB(v___x_3216_, v_type_2562_, v___x_3213_);
lean_inc(v___y_3198_);
lean_inc(v_val_2646_);
v___x_3218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkSemiringInst_x3f___redArg(v_val_2646_, v_type_2562_, v___y_3198_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__60));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_3220_, v_val_2646_, v_type_2562_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOne_x3f(v_val_2646_, v_type_2562_, v___y_3181_, v___y_3194_, v___y_3187_, v___y_3186_, v___y_3199_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
lean_inc(v___y_3185_);
lean_inc(v_a_2660_);
lean_inc(v_a_2657_);
lean_inc(v_a_3219_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkOrderedRingInst_x3f___redArg(v_val_2646_, v_type_2562_, v_a_3219_, v_a_2657_, v_a_2660_, v___y_3185_, v___y_3199_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3225_) == 0)
{
if (lean_obj_tag(v_a_3219_) == 1)
{
lean_object* v_a_3226_; lean_object* v_val_3227_; lean_object* v___x_3228_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v_val_3227_ = lean_ctor_get(v_a_3219_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v_a_3219_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_3228_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_2646_, v_type_2562_, v_val_3227_, v___y_3199_, v___y_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3188_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___y_2872_ = v___x_3217_;
v___y_2873_ = v_a_3222_;
v___y_2874_ = v___y_3182_;
v___y_2875_ = v___x_3214_;
v___y_2876_ = v___y_3185_;
v___y_2877_ = v___y_3184_;
v___y_2878_ = v_a_3207_;
v___y_2879_ = v___x_3210_;
v___y_2880_ = v___x_3213_;
v___y_2881_ = v___x_3209_;
v___y_2882_ = v___y_3201_;
v___y_2883_ = v___y_3189_;
v___y_2884_ = v___y_3190_;
v___y_2885_ = v_a_3226_;
v___y_2886_ = v_a_3224_;
v___y_2887_ = v___y_3195_;
v___y_2888_ = v___x_3208_;
v___y_2889_ = v___y_3196_;
v___y_2890_ = v___y_3198_;
v___y_2891_ = v___y_3197_;
v___y_2892_ = v___y_3200_;
v_charInst_x3f_2893_ = v_a_3229_;
v___y_2894_ = v___y_3181_;
v___y_2895_ = v___y_3194_;
v___y_2896_ = v___y_3187_;
v___y_2897_ = v___y_3186_;
v___y_2898_ = v___y_3199_;
v___y_2899_ = v___y_3183_;
v___y_2900_ = v___y_3191_;
v___y_2901_ = v___y_3192_;
v___y_2902_ = v___y_3193_;
v___y_2903_ = v___y_3188_;
goto v___jp_2871_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_a_3226_);
lean_dec(v_a_3224_);
lean_dec(v_a_3222_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3207_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3230_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3228_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3228_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
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
lean_object* v_a_3238_; lean_object* v___x_3239_; 
lean_dec(v_a_3219_);
v_a_3238_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3239_ = lean_box(0);
v___y_2872_ = v___x_3217_;
v___y_2873_ = v_a_3222_;
v___y_2874_ = v___y_3182_;
v___y_2875_ = v___x_3214_;
v___y_2876_ = v___y_3185_;
v___y_2877_ = v___y_3184_;
v___y_2878_ = v_a_3207_;
v___y_2879_ = v___x_3210_;
v___y_2880_ = v___x_3213_;
v___y_2881_ = v___x_3209_;
v___y_2882_ = v___y_3201_;
v___y_2883_ = v___y_3189_;
v___y_2884_ = v___y_3190_;
v___y_2885_ = v_a_3238_;
v___y_2886_ = v_a_3224_;
v___y_2887_ = v___y_3195_;
v___y_2888_ = v___x_3208_;
v___y_2889_ = v___y_3196_;
v___y_2890_ = v___y_3198_;
v___y_2891_ = v___y_3197_;
v___y_2892_ = v___y_3200_;
v_charInst_x3f_2893_ = v___x_3239_;
v___y_2894_ = v___y_3181_;
v___y_2895_ = v___y_3194_;
v___y_2896_ = v___y_3187_;
v___y_2897_ = v___y_3186_;
v___y_2898_ = v___y_3199_;
v___y_2899_ = v___y_3183_;
v___y_2900_ = v___y_3191_;
v___y_2901_ = v___y_3192_;
v___y_2902_ = v___y_3193_;
v___y_2903_ = v___y_3188_;
goto v___jp_2871_;
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_a_3224_);
lean_dec(v_a_3222_);
lean_dec(v_a_3219_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3207_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3240_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3225_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3225_);
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
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_a_3222_);
lean_dec(v_a_3219_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3207_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3248_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3223_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3223_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3219_);
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3207_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3256_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3221_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3221_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v___x_3213_);
lean_dec(v_a_3207_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3264_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3218_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3218_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3272_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3206_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3206_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec(v___y_3182_);
lean_dec(v_a_3179_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3280_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3203_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3203_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
v___jp_3288_:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_3293_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; uint8_t v_ring_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v_ring_3312_ = lean_ctor_get_uint8(v_a_3311_, sizeof(void*)*14 + 21);
lean_dec(v_a_3311_);
if (v_ring_3312_ == 0)
{
lean_dec_ref(v___f_2640_);
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3309_;
v___y_3186_ = v___y_3294_;
v___y_3187_ = v___y_3293_;
v___y_3188_ = v___y_3295_;
v___y_3189_ = v___y_3296_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3301_;
v___y_3194_ = v___y_3302_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v___y_3307_;
v___y_3200_ = v___y_3308_;
v___y_3201_ = v_ring_3312_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3313_ = lean_box(0);
v___x_3314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__2(v_a_2651_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v___f_2640_);
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3309_;
v___y_3186_ = v___y_3294_;
v___y_3187_ = v___y_3293_;
v___y_3188_ = v___y_3295_;
v___y_3189_ = v___y_3296_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3301_;
v___y_3194_ = v___y_3302_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v___y_3307_;
v___y_3200_ = v___y_3308_;
v___y_3201_ = v___x_3314_;
goto v___jp_3180_;
}
else
{
if (lean_obj_tag(v___y_3309_) == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v___x_3315_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3316_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3315_, v___f_2640_, v___y_3289_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3324_; 
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; 
v_unused_3325_ = lean_ctor_get(v___x_3316_, 0);
lean_dec(v_unused_3325_);
v___x_3318_ = v___x_3316_;
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v___x_3316_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = lean_box(0);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
v_a_3326_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3316_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3316_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_dec_ref(v___f_2640_);
v___y_3181_ = v___y_3289_;
v___y_3182_ = v___y_3290_;
v___y_3183_ = v___y_3291_;
v___y_3184_ = v___y_3292_;
v___y_3185_ = v___y_3309_;
v___y_3186_ = v___y_3294_;
v___y_3187_ = v___y_3293_;
v___y_3188_ = v___y_3295_;
v___y_3189_ = v___y_3296_;
v___y_3190_ = v___y_3298_;
v___y_3191_ = v___y_3299_;
v___y_3192_ = v___y_3300_;
v___y_3193_ = v___y_3301_;
v___y_3194_ = v___y_3302_;
v___y_3195_ = v___y_3303_;
v___y_3196_ = v___y_3304_;
v___y_3197_ = v___y_3306_;
v___y_3198_ = v___y_3305_;
v___y_3199_ = v___y_3307_;
v___y_3200_ = v___y_3308_;
v___y_3201_ = v___y_3297_;
goto v___jp_3180_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v_a_3179_);
lean_dec(v_a_3177_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3334_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3310_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3310_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
v___jp_3342_:
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_box(0);
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
v___y_3301_ = v___y_3355_;
v___y_3302_ = v___y_3356_;
v___y_3303_ = v___y_3357_;
v___y_3304_ = v___y_3358_;
v___y_3305_ = v___y_3360_;
v___y_3306_ = v___y_3359_;
v___y_3307_ = v___y_3361_;
v___y_3308_ = v___y_3362_;
v___y_3309_ = v___x_3363_;
goto v___jp_3288_;
}
v___jp_3364_:
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_box(0);
v___y_3343_ = v___y_3374_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3379_;
v___y_3346_ = v___x_3384_;
v___y_3347_ = v___y_3376_;
v___y_3348_ = v___y_3377_;
v___y_3349_ = v___y_3383_;
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___y_3366_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3381_;
v___y_3355_ = v___y_3382_;
v___y_3356_ = v___y_3375_;
v___y_3357_ = v___y_3368_;
v___y_3358_ = v___y_3369_;
v___y_3359_ = v___y_3371_;
v___y_3360_ = v___y_3370_;
v___y_3361_ = v___y_3378_;
v___y_3362_ = v___y_3373_;
goto v___jp_3342_;
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_a_3177_);
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3504_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3178_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3178_);
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
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v_a_3175_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3512_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3176_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3176_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
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
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3520_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3174_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3174_);
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
v___jp_2663_:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_2689_, v___y_2697_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v_structs_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v_structs_2701_ = lean_ctor_get(v_a_2700_, 0);
lean_inc_ref(v_structs_2701_);
lean_dec(v_a_2700_);
v___x_2702_ = lean_array_get_size(v_structs_2701_);
lean_dec_ref(v_structs_2701_);
v___x_2703_ = lean_unsigned_to_nat(32u);
v___x_2704_ = lean_mk_empty_array_with_capacity(v___x_2703_);
v___x_2705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_2706_ = ((size_t)5ULL);
lean_inc(v___y_2669_);
v___x_2707_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2704_);
lean_ctor_set(v___x_2707_, 2, v___y_2669_);
lean_ctor_set(v___x_2707_, 3, v___y_2669_);
lean_ctor_set_usize(v___x_2707_, 4, v___x_2706_);
v___x_2708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_box(0);
lean_inc_ref_n(v___x_2707_, 7);
lean_inc(v___y_2680_);
lean_inc(v___y_2687_);
lean_inc(v___y_2666_);
lean_inc(v___y_2679_);
lean_inc(v___y_2683_);
v___x_2711_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_2711_, 0, v___x_2702_);
lean_ctor_set(v___x_2711_, 1, v_a_2651_);
lean_ctor_set(v___x_2711_, 2, v_type_2562_);
lean_ctor_set(v___x_2711_, 3, v_val_2646_);
lean_ctor_set(v___x_2711_, 4, v___y_2682_);
lean_ctor_set(v___x_2711_, 5, v_a_2657_);
lean_ctor_set(v___x_2711_, 6, v_a_2660_);
lean_ctor_set(v___x_2711_, 7, v_a_2662_);
lean_ctor_set(v___x_2711_, 8, v___y_2670_);
lean_ctor_set(v___x_2711_, 9, v___y_2671_);
lean_ctor_set(v___x_2711_, 10, v___y_2672_);
lean_ctor_set(v___x_2711_, 11, v___y_2668_);
lean_ctor_set(v___x_2711_, 12, v___y_2683_);
lean_ctor_set(v___x_2711_, 13, v___y_2681_);
lean_ctor_set(v___x_2711_, 14, v___y_2679_);
lean_ctor_set(v___x_2711_, 15, v___y_2666_);
lean_ctor_set(v___x_2711_, 16, v___y_2687_);
lean_ctor_set(v___x_2711_, 17, v___y_2678_);
lean_ctor_set(v___x_2711_, 18, v___y_2667_);
lean_ctor_set(v___x_2711_, 19, v___y_2680_);
lean_ctor_set(v___x_2711_, 20, v___y_2685_);
lean_ctor_set(v___x_2711_, 21, v___y_2684_);
lean_ctor_set(v___x_2711_, 22, v___y_2677_);
lean_ctor_set(v___x_2711_, 23, v___y_2665_);
lean_ctor_set(v___x_2711_, 24, v___y_2676_);
lean_ctor_set(v___x_2711_, 25, v___y_2675_);
lean_ctor_set(v___x_2711_, 26, v___y_2686_);
lean_ctor_set(v___x_2711_, 27, v_homomulFn_x3f_2688_);
lean_ctor_set(v___x_2711_, 28, v___y_2664_);
lean_ctor_set(v___x_2711_, 29, v___y_2673_);
lean_ctor_set(v___x_2711_, 30, v___x_2707_);
lean_ctor_set(v___x_2711_, 31, v___x_2708_);
lean_ctor_set(v___x_2711_, 32, v___x_2707_);
lean_ctor_set(v___x_2711_, 33, v___x_2707_);
lean_ctor_set(v___x_2711_, 34, v___x_2707_);
lean_ctor_set(v___x_2711_, 35, v___x_2707_);
lean_ctor_set(v___x_2711_, 36, v___x_2709_);
lean_ctor_set(v___x_2711_, 37, v___x_2708_);
lean_ctor_set(v___x_2711_, 38, v___x_2707_);
lean_ctor_set(v___x_2711_, 39, v___x_2710_);
lean_ctor_set(v___x_2711_, 40, v___x_2707_);
lean_ctor_set(v___x_2711_, 41, v___x_2707_);
lean_ctor_set_uint8(v___x_2711_, sizeof(void*)*42, v___y_2674_);
v___f_2712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_2712_, 0, v___x_2711_);
v___x_2713_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2713_, v___f_2712_, v___y_2689_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_dec_ref_known(v___x_2714_, 1);
if (lean_obj_tag(v___y_2680_) == 1)
{
if (lean_obj_tag(v___y_2683_) == 0)
{
lean_dec_ref_known(v___y_2680_, 1);
lean_dec(v___y_2687_);
lean_dec(v___y_2679_);
lean_dec(v___y_2666_);
v___y_2575_ = v___x_2702_;
goto v___jp_2574_;
}
else
{
lean_dec_ref_known(v___y_2683_, 1);
if (lean_obj_tag(v___y_2679_) == 0)
{
if (v___y_2674_ == 0)
{
if (lean_obj_tag(v___y_2666_) == 0)
{
lean_object* v_val_2715_; uint8_t v___x_2716_; 
v_val_2715_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v___y_2680_, 1);
v___x_2716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isNonTrivialIsCharInst(v___y_2687_);
lean_dec(v___y_2687_);
if (v___x_2716_ == 0)
{
lean_dec(v_val_2715_);
v___y_2575_ = v___x_2702_;
goto v___jp_2574_;
}
else
{
v___y_2616_ = v___y_2691_;
v___y_2617_ = v___y_2692_;
v___y_2618_ = v___y_2695_;
v___y_2619_ = v___y_2689_;
v___y_2620_ = v___y_2674_;
v___y_2621_ = v___y_2694_;
v___y_2622_ = v___y_2698_;
v___y_2623_ = v___y_2693_;
v___y_2624_ = v___y_2697_;
v___y_2625_ = v___y_2690_;
v___y_2626_ = v_val_2715_;
v___y_2627_ = v___x_2702_;
v___y_2628_ = v___y_2696_;
goto v___jp_2615_;
}
}
else
{
lean_object* v_val_2717_; 
lean_dec_ref_known(v___y_2666_, 1);
lean_dec(v___y_2687_);
v_val_2717_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_val_2717_);
lean_dec_ref_known(v___y_2680_, 1);
v___y_2616_ = v___y_2691_;
v___y_2617_ = v___y_2692_;
v___y_2618_ = v___y_2695_;
v___y_2619_ = v___y_2689_;
v___y_2620_ = v___y_2674_;
v___y_2621_ = v___y_2694_;
v___y_2622_ = v___y_2698_;
v___y_2623_ = v___y_2693_;
v___y_2624_ = v___y_2697_;
v___y_2625_ = v___y_2690_;
v___y_2626_ = v_val_2717_;
v___y_2627_ = v___x_2702_;
v___y_2628_ = v___y_2696_;
goto v___jp_2615_;
}
}
else
{
lean_object* v_val_2718_; 
lean_dec(v___y_2687_);
lean_dec(v___y_2666_);
v_val_2718_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v___y_2680_, 1);
v___y_2590_ = v___y_2691_;
v___y_2591_ = v___y_2692_;
v___y_2592_ = v___y_2695_;
v___y_2593_ = v___y_2689_;
v___y_2594_ = v___y_2674_;
v___y_2595_ = v___y_2694_;
v___y_2596_ = v___y_2698_;
v___y_2597_ = v___y_2693_;
v___y_2598_ = v___y_2697_;
v___y_2599_ = v___y_2690_;
v___y_2600_ = v_val_2718_;
v___y_2601_ = v___x_2702_;
v___y_2602_ = v___y_2696_;
goto v___jp_2589_;
}
}
else
{
lean_object* v_val_2719_; 
lean_dec_ref_known(v___y_2679_, 1);
lean_dec(v___y_2687_);
lean_dec(v___y_2666_);
v_val_2719_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___y_2680_, 1);
v___y_2590_ = v___y_2691_;
v___y_2591_ = v___y_2692_;
v___y_2592_ = v___y_2695_;
v___y_2593_ = v___y_2689_;
v___y_2594_ = v___y_2674_;
v___y_2595_ = v___y_2694_;
v___y_2596_ = v___y_2698_;
v___y_2597_ = v___y_2693_;
v___y_2598_ = v___y_2697_;
v___y_2599_ = v___y_2690_;
v___y_2600_ = v_val_2719_;
v___y_2601_ = v___x_2702_;
v___y_2602_ = v___y_2696_;
goto v___jp_2589_;
}
}
}
else
{
lean_dec(v___y_2687_);
lean_dec(v___y_2683_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v___y_2666_);
v___y_2575_ = v___x_2702_;
goto v___jp_2574_;
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v___y_2687_);
lean_dec(v___y_2683_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec(v___y_2666_);
v_a_2720_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2714_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2714_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_homomulFn_x3f_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v_a_2651_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2728_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2699_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2699_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2771_; 
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg(v_val_2646_, v_type_2562_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2773_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatFn_x3f___redArg(v_val_2646_, v_type_2562_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2773_) == 0)
{
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v_a_2774_; 
lean_dec(v___y_2749_);
lean_del_object(v___x_2648_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___y_2664_ = v___y_2737_;
v___y_2665_ = v___y_2738_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2743_;
v___y_2671_ = v___y_2744_;
v___y_2672_ = v___y_2745_;
v___y_2673_ = v___y_2746_;
v___y_2674_ = v___y_2747_;
v___y_2675_ = v_a_2772_;
v___y_2676_ = v___y_2748_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2751_;
v___y_2679_ = v___y_2752_;
v___y_2680_ = v___y_2753_;
v___y_2681_ = v___y_2754_;
v___y_2682_ = v___y_2756_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v_ltFn_x3f_2760_;
v___y_2685_ = v___y_2758_;
v___y_2686_ = v_a_2774_;
v___y_2687_ = v___y_2759_;
v_homomulFn_x3f_2688_ = v___y_2757_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2766_;
v___y_2695_ = v___y_2767_;
v___y_2696_ = v___y_2768_;
v___y_2697_ = v___y_2769_;
v___y_2698_ = v___y_2770_;
goto v___jp_2663_;
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v___y_2757_);
v_a_2775_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__8));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2776_, v_val_2646_, v_type_2562_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__10));
v___x_2780_ = l_Lean_mkConst(v___x_2779_, v___y_2749_);
lean_inc_ref_n(v_type_2562_, 3);
v___x_2781_ = l_Lean_mkApp4(v___x_2780_, v_type_2562_, v_type_2562_, v_type_2562_, v_a_2778_);
v___x_2782_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2781_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_a_2783_);
v___x_2785_ = v___x_2648_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
v___y_2664_ = v___y_2737_;
v___y_2665_ = v___y_2738_;
v___y_2666_ = v___y_2739_;
v___y_2667_ = v___y_2740_;
v___y_2668_ = v___y_2741_;
v___y_2669_ = v___y_2742_;
v___y_2670_ = v___y_2743_;
v___y_2671_ = v___y_2744_;
v___y_2672_ = v___y_2745_;
v___y_2673_ = v___y_2746_;
v___y_2674_ = v___y_2747_;
v___y_2675_ = v_a_2772_;
v___y_2676_ = v___y_2748_;
v___y_2677_ = v___y_2750_;
v___y_2678_ = v___y_2751_;
v___y_2679_ = v___y_2752_;
v___y_2680_ = v___y_2753_;
v___y_2681_ = v___y_2754_;
v___y_2682_ = v___y_2756_;
v___y_2683_ = v___y_2755_;
v___y_2684_ = v_ltFn_x3f_2760_;
v___y_2685_ = v___y_2758_;
v___y_2686_ = v_a_2775_;
v___y_2687_ = v___y_2759_;
v_homomulFn_x3f_2688_ = v___x_2785_;
v___y_2689_ = v___y_2761_;
v___y_2690_ = v___y_2762_;
v___y_2691_ = v___y_2763_;
v___y_2692_ = v___y_2764_;
v___y_2693_ = v___y_2765_;
v___y_2694_ = v___y_2766_;
v___y_2695_ = v___y_2767_;
v___y_2696_ = v___y_2768_;
v___y_2697_ = v___y_2769_;
v___y_2698_ = v___y_2770_;
goto v___jp_2663_;
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2775_);
lean_dec_ref_known(v___y_2754_, 1);
lean_dec(v_a_2772_);
lean_dec(v_ltFn_x3f_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2787_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2782_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2782_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2775_);
lean_dec_ref_known(v___y_2754_, 1);
lean_dec(v_a_2772_);
lean_dec(v_ltFn_x3f_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2795_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2777_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2777_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2772_);
lean_dec(v_ltFn_x3f_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2803_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2773_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2773_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_ltFn_x3f_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2811_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2771_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2771_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
v___jp_2819_:
{
if (lean_obj_tag(v_a_2660_) == 1)
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_val_2854_ = lean_ctor_get(v_a_2660_, 0);
v___x_2855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_2856_ = l_Lean_mkConst(v___x_2855_, v___y_2824_);
lean_inc(v_val_2854_);
lean_inc_ref(v_type_2562_);
v___x_2857_ = l_Lean_mkAppB(v___x_2856_, v_type_2562_, v_val_2854_);
v___x_2858_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2857_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
lean_ctor_set(v___x_2653_, 0, v_a_2859_);
v___x_2861_ = v___x_2653_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
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
v___y_2751_ = v___y_2835_;
v___y_2752_ = v___y_2836_;
v___y_2753_ = v___y_2837_;
v___y_2754_ = v___y_2838_;
v___y_2755_ = v___y_2840_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2841_;
v___y_2758_ = v_leFn_x3f_2843_;
v___y_2759_ = v___y_2842_;
v_ltFn_x3f_2760_ = v___x_2861_;
v___y_2761_ = v___y_2844_;
v___y_2762_ = v___y_2845_;
v___y_2763_ = v___y_2846_;
v___y_2764_ = v___y_2847_;
v___y_2765_ = v___y_2848_;
v___y_2766_ = v___y_2849_;
v___y_2767_ = v___y_2850_;
v___y_2768_ = v___y_2851_;
v___y_2769_ = v___y_2852_;
v___y_2770_ = v___y_2853_;
goto v___jp_2736_;
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref_known(v_a_2660_, 1);
lean_dec(v_leFn_x3f_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_a_2662_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_2863_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2858_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2858_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_dec(v___y_2824_);
lean_del_object(v___x_2653_);
lean_inc(v___y_2841_);
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
v___y_2751_ = v___y_2835_;
v___y_2752_ = v___y_2836_;
v___y_2753_ = v___y_2837_;
v___y_2754_ = v___y_2838_;
v___y_2755_ = v___y_2840_;
v___y_2756_ = v___y_2839_;
v___y_2757_ = v___y_2841_;
v___y_2758_ = v_leFn_x3f_2843_;
v___y_2759_ = v___y_2842_;
v_ltFn_x3f_2760_ = v___y_2841_;
v___y_2761_ = v___y_2844_;
v___y_2762_ = v___y_2845_;
v___y_2763_ = v___y_2846_;
v___y_2764_ = v___y_2847_;
v___y_2765_ = v___y_2848_;
v___y_2766_ = v___y_2849_;
v___y_2767_ = v___y_2850_;
v___y_2768_ = v___y_2851_;
v___y_2769_ = v___y_2852_;
v___y_2770_ = v___y_2853_;
goto v___jp_2736_;
}
}
v___jp_2871_:
{
lean_object* v___x_2904_; 
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2904_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg(v_val_2646_, v_type_2562_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2906_, v_val_2646_, v_type_2562_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_n(v_a_2908_, 2);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
lean_inc(v___y_2874_);
v___x_2910_ = l_Lean_mkConst(v___x_2909_, v___y_2874_);
lean_inc_ref(v_type_2562_);
v___x_2911_ = l_Lean_mkAppB(v___x_2910_, v_type_2562_, v_a_2908_);
v___x_2912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_2911_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_2874_);
v___x_2915_ = l_Lean_mkConst(v___x_2914_, v___y_2874_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_2562_);
v___x_2918_ = l_Lean_mkAppB(v___x_2915_, v_type_2562_, v___x_2917_);
v___x_2919_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2918_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_3141_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_2922_ = v___x_2919_;
v_isShared_2923_ = v_isSharedCheck_3141_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_3141_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
if (lean_obj_tag(v_a_2920_) == 1)
{
lean_object* v_val_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_3136_; 
lean_del_object(v___x_2922_);
v_val_2924_ = lean_ctor_get(v_a_2920_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_2920_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_2926_ = v_a_2920_;
v_isShared_2927_ = v_isSharedCheck_3136_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_val_2924_);
lean_dec(v_a_2920_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_3136_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__21));
lean_inc(v___y_2874_);
v___x_2929_ = l_Lean_mkConst(v___x_2928_, v___y_2874_);
lean_inc_ref(v_type_2562_);
v___x_2930_ = l_Lean_mkApp3(v___x_2929_, v_type_2562_, v___x_2917_, v_val_2924_);
v___x_2931_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2930_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_n(v_a_2932_, 2);
lean_dec_ref_known(v___x_2931_, 1);
lean_inc(v_a_2913_);
v___x_2933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq(v_a_2913_, v_a_2932_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2933_, 1);
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2935_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_2934_, v_val_2646_, v_type_2562_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_n(v_a_2936_, 2);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__25));
lean_inc(v___y_2883_);
v___x_2938_ = l_Lean_mkConst(v___x_2937_, v___y_2883_);
lean_inc_ref_n(v_type_2562_, 3);
v___x_2939_ = l_Lean_mkApp4(v___x_2938_, v_type_2562_, v_type_2562_, v_type_2562_, v_a_2936_);
v___x_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2939_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_2942_, v_val_2646_, v_type_2562_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_n(v_a_2944_, 2);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__29));
lean_inc(v___y_2874_);
v___x_2946_ = l_Lean_mkConst(v___x_2945_, v___y_2874_);
lean_inc_ref(v_type_2562_);
v___x_2947_ = l_Lean_mkAppB(v___x_2946_, v_type_2562_, v_a_2944_);
v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2947_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg(v_val_2646_, v_type_2562_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc_n(v_a_2951_, 2);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_2953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v___y_2889_);
v___x_2955_ = l_Lean_mkConst(v___x_2952_, v___x_2954_);
v___x_2956_ = l_Lean_Int_mkType;
lean_inc_ref_n(v_type_2562_, 2);
lean_inc_ref(v___x_2955_);
v___x_2957_ = l_Lean_mkApp4(v___x_2955_, v___x_2956_, v_type_2562_, v_type_2562_, v_a_2951_);
v___x_2958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2957_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_val_2646_, v_type_2562_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc_n(v_a_2961_, 2);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2562_, 2);
v___x_2963_ = l_Lean_mkApp4(v___x_2955_, v___x_2962_, v_type_2562_, v_type_2562_, v_a_2961_);
v___x_2964_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2963_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__30));
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__31));
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2968_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___x_2966_, v___x_2967_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc_ref(v___y_2872_);
v___x_2969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2908_, v___y_2872_, v___x_2968_, v_val_2646_, v_type_2562_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__32));
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2971_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___x_2966_, v___x_2970_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_2973_ = lean_box(0);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2974_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v___y_2892_, v___y_2872_, v___x_2971_, v___x_2972_, v_val_2646_, v_type_2562_, v___x_2973_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref_known(v___x_2974_, 1);
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__35));
lean_inc_ref(v___y_2875_);
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2976_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___y_2875_, v___x_2975_);
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc_ref(v___y_2880_);
v___x_2978_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2936_, v___y_2880_, v___x_2976_, v___x_2977_, v_val_2646_, v_type_2562_, v___x_2973_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec_ref_known(v___x_2978_, 1);
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__38));
lean_inc_ref(v___y_2875_);
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2980_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___y_2875_, v___x_2979_);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
v___x_2981_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToFieldDefEq___redArg(v_a_2944_, v___y_2880_, v___x_2980_, v_val_2646_, v_type_2562_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec_ref_known(v___x_2981_, 1);
v___x_2982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__39));
lean_inc_ref(v___y_2879_);
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2983_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___y_2879_, v___x_2982_);
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_2985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__42);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc_ref(v___y_2891_);
v___x_2986_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2951_, v___y_2891_, v___x_2983_, v___x_2984_, v_val_2646_, v_type_2562_, v___x_2985_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec_ref_known(v___x_2986_, 1);
v___x_2987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__43));
lean_inc_ref(v___y_2879_);
lean_inc_ref(v___y_2881_);
lean_inc_ref(v___y_2888_);
v___x_2988_ = l_Lean_Name_mkStr4(v___y_2888_, v___y_2881_, v___y_2879_, v___x_2987_);
v___x_2989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__44);
lean_inc_ref(v_type_2562_);
lean_inc(v_val_2646_);
lean_inc_ref(v___y_2891_);
v___x_2990_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureToHomoFieldDefEq___redArg(v_a_2961_, v___y_2891_, v___x_2988_, v___x_2984_, v_val_2646_, v_type_2562_, v___x_2989_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref_known(v___x_2990_, 1);
if (lean_obj_tag(v_a_2657_) == 1)
{
lean_object* v_val_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_val_2991_ = lean_ctor_get(v_a_2657_, 0);
v___x_2992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_2874_);
v___x_2993_ = l_Lean_mkConst(v___x_2992_, v___y_2874_);
lean_inc(v_val_2991_);
lean_inc_ref(v_type_2562_);
v___x_2994_ = l_Lean_mkAppB(v___x_2993_, v_type_2562_, v_val_2991_);
v___x_2995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_2994_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v_a_2996_);
v___x_2998_ = v___x_2926_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
v___y_2820_ = v_a_2941_;
v___y_2821_ = v_a_2959_;
v___y_2822_ = v___y_2873_;
v___y_2823_ = v_a_2932_;
v___y_2824_ = v___y_2874_;
v___y_2825_ = v_a_2905_;
v___y_2826_ = v___x_2916_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v_a_2949_;
v___y_2831_ = v___y_2882_;
v___y_2832_ = v_a_2965_;
v___y_2833_ = v___y_2883_;
v___y_2834_ = v___y_2884_;
v___y_2835_ = v_a_2913_;
v___y_2836_ = v___y_2885_;
v___y_2837_ = v___y_2886_;
v___y_2838_ = v___y_2887_;
v___y_2839_ = v___y_2891_;
v___y_2840_ = v___y_2890_;
v___y_2841_ = v___x_2973_;
v___y_2842_ = v_charInst_x3f_2893_;
v_leFn_x3f_2843_ = v___x_2998_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v___y_2895_;
v___y_2846_ = v___y_2896_;
v___y_2847_ = v___y_2897_;
v___y_2848_ = v___y_2898_;
v___y_2849_ = v___y_2899_;
v___y_2850_ = v___y_2900_;
v___y_2851_ = v___y_2901_;
v___y_2852_ = v___y_2902_;
v___y_2853_ = v___y_2903_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref_known(v_a_2657_, 1);
lean_dec(v_a_2965_);
lean_dec(v_a_2959_);
lean_dec(v_a_2949_);
lean_dec(v_a_2941_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3000_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2995_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2995_);
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
lean_del_object(v___x_2926_);
v___y_2820_ = v_a_2941_;
v___y_2821_ = v_a_2959_;
v___y_2822_ = v___y_2873_;
v___y_2823_ = v_a_2932_;
v___y_2824_ = v___y_2874_;
v___y_2825_ = v_a_2905_;
v___y_2826_ = v___x_2916_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v_a_2949_;
v___y_2831_ = v___y_2882_;
v___y_2832_ = v_a_2965_;
v___y_2833_ = v___y_2883_;
v___y_2834_ = v___y_2884_;
v___y_2835_ = v_a_2913_;
v___y_2836_ = v___y_2885_;
v___y_2837_ = v___y_2886_;
v___y_2838_ = v___y_2887_;
v___y_2839_ = v___y_2891_;
v___y_2840_ = v___y_2890_;
v___y_2841_ = v___x_2973_;
v___y_2842_ = v_charInst_x3f_2893_;
v_leFn_x3f_2843_ = v___x_2973_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v___y_2895_;
v___y_2846_ = v___y_2896_;
v___y_2847_ = v___y_2897_;
v___y_2848_ = v___y_2898_;
v___y_2849_ = v___y_2899_;
v___y_2850_ = v___y_2900_;
v___y_2851_ = v___y_2901_;
v___y_2852_ = v___y_2902_;
v___y_2853_ = v___y_2903_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_a_2965_);
lean_dec(v_a_2959_);
lean_dec(v_a_2949_);
lean_dec(v_a_2941_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3008_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2990_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2990_);
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
lean_dec(v_a_2965_);
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2949_);
lean_dec(v_a_2941_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3016_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2986_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2986_);
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
lean_dec(v_a_2965_);
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2941_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3024_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2981_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2981_);
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
lean_dec(v_a_2965_);
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3032_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2978_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2978_);
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
lean_dec(v_a_2965_);
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3040_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2974_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2974_);
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
lean_dec(v_a_2965_);
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3048_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2969_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2969_);
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
lean_dec(v_a_2961_);
lean_dec(v_a_2959_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3056_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2964_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2964_);
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
lean_dec(v_a_2959_);
lean_dec_ref(v___x_2955_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3064_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2960_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2960_);
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
lean_dec_ref(v___x_2955_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3072_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2958_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_2958_);
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
lean_dec(v_a_2949_);
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3080_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2950_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2950_);
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
lean_dec(v_a_2944_);
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3088_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_2948_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_2948_);
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
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_2941_);
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3096_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_2943_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_2943_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_2936_);
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3104_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_2940_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_2940_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3112_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_2935_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_2935_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_a_2932_);
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3120_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_2933_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_2933_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_del_object(v___x_2926_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3128_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_2931_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_2931_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_dec(v_a_2920_);
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v___x_3137_ = lean_box(0);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_3137_);
v___x_3139_ = v___x_2922_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_a_2913_);
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3142_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_2919_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_2919_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_a_2908_);
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3150_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_2912_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_2912_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_a_2905_);
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3158_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_2907_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_2907_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_charInst_x3f_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_a_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v_type_2562_);
v_a_3166_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_2904_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_2904_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_a_2660_);
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3528_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_2661_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_2661_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_a_2657_);
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3536_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_2659_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_2659_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_del_object(v___x_2653_);
lean_dec(v_a_2651_);
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3544_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_2656_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_2656_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
else
{
lean_del_object(v___x_2648_);
lean_dec(v_val_2646_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
return v___x_2650_;
}
}
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec(v_a_2642_);
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v___x_3554_ = lean_box(0);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_3554_);
v___x_3556_ = v___x_2644_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v___f_2640_);
lean_dec_ref(v_type_2562_);
v_a_3559_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_2641_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_2641_);
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
v___jp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
v___jp_2578_:
{
if (lean_obj_tag(v___y_2580_) == 0)
{
lean_dec_ref_known(v___y_2580_, 1);
v___y_2575_ = v___y_2579_;
goto v___jp_2574_;
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v___y_2579_);
v_a_2581_ = lean_ctor_get(v___y_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___y_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___y_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___y_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
v___jp_2589_:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2600_, v___y_2594_, v___y_2601_, v___y_2593_, v___y_2599_, v___y_2590_, v___y_2591_, v___y_2597_, v___y_2595_, v___y_2592_, v___y_2602_, v___y_2598_, v___y_2596_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc_n(v_a_2604_, 2);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroLtOne___redArg(v_a_2604_, v___y_2601_, v___y_2593_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2606_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2604_, v___y_2601_, v___y_2593_);
v___y_2579_ = v___y_2601_;
v___y_2580_ = v___x_2606_;
goto v___jp_2578_;
}
else
{
lean_dec(v_a_2604_);
v___y_2579_ = v___y_2601_;
v___y_2580_ = v___x_2605_;
goto v___jp_2578_;
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v___y_2601_);
v_a_2607_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2603_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2603_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_Meta_Grind_Arith_Linear_mkVar(v___y_2626_, v___y_2620_, v___y_2627_, v___y_2619_, v___y_2625_, v___y_2616_, v___y_2617_, v___y_2623_, v___y_2621_, v___y_2618_, v___y_2628_, v___y_2624_, v___y_2622_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_addZeroNeOne___redArg(v_a_2630_, v___y_2627_, v___y_2619_);
v___y_2579_ = v___y_2627_;
v___y_2580_ = v___x_2631_;
goto v___jp_2578_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v___y_2627_);
v_a_2632_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2629_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2629_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___boxed(lean_object* v_type_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
lean_dec(v_a_3569_);
lean_dec(v_a_3568_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_x_3581_, v_x_3582_, v_x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_3585_, lean_object* v_x_3586_, size_t v_x_3587_, size_t v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___redArg(v_x_3586_, v_x_3587_, v_x_3588_, v_x_3589_, v_x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
size_t v_x_530316__boxed_3598_; size_t v_x_530317__boxed_3599_; lean_object* v_res_3600_; 
v_x_530316__boxed_3598_ = lean_unbox_usize(v_x_3594_);
lean_dec(v_x_3594_);
v_x_530317__boxed_3599_ = lean_unbox_usize(v_x_3595_);
lean_dec(v_x_3595_);
v_res_3600_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0(v_00_u03b2_3592_, v_x_3593_, v_x_530316__boxed_3598_, v_x_530317__boxed_3599_, v_x_3596_, v_x_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3601_, lean_object* v_n_3602_, lean_object* v_k_3603_, lean_object* v_v_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1___redArg(v_n_3602_, v_k_3603_, v_v_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3606_, size_t v_depth_3607_, lean_object* v_keys_3608_, lean_object* v_vals_3609_, lean_object* v_heq_3610_, lean_object* v_i_3611_, lean_object* v_entries_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___redArg(v_depth_3607_, v_keys_3608_, v_vals_3609_, v_i_3611_, v_entries_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3614_, lean_object* v_depth_3615_, lean_object* v_keys_3616_, lean_object* v_vals_3617_, lean_object* v_heq_3618_, lean_object* v_i_3619_, lean_object* v_entries_3620_){
_start:
{
size_t v_depth_boxed_3621_; lean_object* v_res_3622_; 
v_depth_boxed_3621_ = lean_unbox_usize(v_depth_3615_);
lean_dec(v_depth_3615_);
v_res_3622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__2(v_00_u03b2_3614_, v_depth_boxed_3621_, v_keys_3616_, v_vals_3617_, v_heq_3618_, v_i_3619_, v_entries_3620_);
lean_dec_ref(v_vals_3617_);
lean_dec_ref(v_keys_3616_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3624_, v_x_3625_, v_x_3626_, v_x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(lean_object* v_val_3629_, lean_object* v_base_3630_, lean_object* v_natModuleInst_3631_, lean_object* v_declName_3632_, lean_object* v_le_3633_, lean_object* v_mid_3634_, lean_object* v_ord_3635_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3636_ = lean_box(0);
v___x_3637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_val_3629_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = l_Lean_mkConst(v_declName_3632_, v___x_3637_);
v___x_3639_ = l_Lean_mkApp5(v___x_3638_, v_base_3630_, v_natModuleInst_3631_, v_le_3633_, v_mid_3634_, v_ord_3635_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(lean_object* v_type_3739_, lean_object* v_base_3740_, lean_object* v_natModuleInst_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3753_; 
lean_inc_ref(v_base_3740_);
v___x_3753_ = l_Lean_Meta_getDecLevel_x3f(v_base_3740_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_4491_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_4491_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_4491_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
if (lean_obj_tag(v_a_3754_) == 1)
{
lean_object* v_val_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_4486_; 
lean_del_object(v___x_3756_);
v_val_3758_ = lean_ctor_get(v_a_3754_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_a_3754_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_3760_ = v_a_3754_;
v_isShared_3761_ = v_isSharedCheck_4486_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_val_3758_);
lean_dec(v_a_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_4486_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_a_3782_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v_a_3854_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___x_4072_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_noNatDivInstQ_x3f_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v_isLinearInstQ_x3f_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___x_4327_; 
v___x_4072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4072_, v_val_3758_, v_base_3740_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v_fst_4339_; lean_object* v_snd_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___x_4380_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc_n(v_a_4328_, 2);
lean_dec_ref_known(v___x_4327_, 1);
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4380_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_3758_, v_base_3740_, v_a_4328_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v_orderedAddInst_x3f_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4380_, 1);
if (lean_obj_tag(v_a_4328_) == 1)
{
if (lean_obj_tag(v_a_4381_) == 1)
{
lean_object* v_val_4442_; lean_object* v_val_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_val_4442_ = lean_ctor_get(v_a_4328_, 0);
v_val_4443_ = lean_ctor_get(v_a_4381_, 0);
v___x_4444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4444_, v_val_3758_, v_base_3740_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref_known(v___x_4445_, 1);
v___x_4447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
v___x_4448_ = lean_box(0);
lean_inc(v_val_3758_);
v___x_4449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4449_, 0, v_val_3758_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l_Lean_mkConst(v___x_4447_, v___x_4449_);
lean_inc(v_val_4443_);
lean_inc(v_val_4442_);
lean_inc_ref(v_base_3740_);
v___x_4451_ = l_Lean_mkApp4(v___x_4450_, v_base_3740_, v_a_4446_, v_val_4442_, v_val_4443_);
v___x_4452_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4451_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v_orderedAddInst_x3f_4383_ = v_a_4453_;
v___y_4384_ = v_a_3742_;
v___y_4385_ = v_a_3743_;
v___y_4386_ = v_a_3744_;
v___y_4387_ = v_a_3745_;
v___y_4388_ = v_a_3746_;
v___y_4389_ = v_a_3747_;
v___y_4390_ = v_a_3748_;
v___y_4391_ = v_a_3749_;
v___y_4392_ = v_a_3750_;
v___y_4393_ = v_a_3751_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec_ref_known(v_a_4381_, 1);
lean_dec_ref_known(v_a_4328_, 1);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4454_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4452_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref_known(v_a_4381_, 1);
lean_dec_ref_known(v_a_4328_, 1);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4462_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4445_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4445_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
else
{
v___y_4431_ = v_a_3742_;
v___y_4432_ = v_a_3743_;
v___y_4433_ = v_a_3744_;
v___y_4434_ = v_a_3745_;
v___y_4435_ = v_a_3746_;
v___y_4436_ = v_a_3747_;
v___y_4437_ = v_a_3748_;
v___y_4438_ = v_a_3749_;
v___y_4439_ = v_a_3750_;
v___y_4440_ = v_a_3751_;
goto v___jp_4430_;
}
}
else
{
v___y_4431_ = v_a_3742_;
v___y_4432_ = v_a_3743_;
v___y_4433_ = v_a_3744_;
v___y_4434_ = v_a_3745_;
v___y_4435_ = v_a_3746_;
v___y_4436_ = v_a_3747_;
v___y_4437_ = v_a_3748_;
v___y_4438_ = v_a_3749_;
v___y_4439_ = v_a_3750_;
v___y_4440_ = v_a_3751_;
goto v___jp_4430_;
}
v___jp_4382_:
{
if (lean_obj_tag(v_a_4328_) == 0)
{
lean_object* v___x_4394_; 
lean_dec(v_orderedAddInst_x3f_4383_);
lean_dec(v_a_4381_);
v___x_4394_ = lean_box(0);
v___y_4368_ = v___y_4389_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4388_;
v___y_4371_ = v___y_4390_;
v___y_4372_ = v___y_4393_;
v___y_4373_ = v___y_4385_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4391_;
v___y_4376_ = v___y_4392_;
v___y_4377_ = v___y_4386_;
v___y_4378_ = v___x_4394_;
goto v___jp_4367_;
}
else
{
if (lean_obj_tag(v_a_4381_) == 0)
{
lean_object* v___x_4395_; 
lean_dec_ref_known(v_a_4328_, 1);
lean_dec(v_orderedAddInst_x3f_4383_);
v___x_4395_ = lean_box(0);
v___y_4368_ = v___y_4389_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4388_;
v___y_4371_ = v___y_4390_;
v___y_4372_ = v___y_4393_;
v___y_4373_ = v___y_4385_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4391_;
v___y_4376_ = v___y_4392_;
v___y_4377_ = v___y_4386_;
v___y_4378_ = v___x_4395_;
goto v___jp_4367_;
}
else
{
if (lean_obj_tag(v_orderedAddInst_x3f_4383_) == 0)
{
lean_object* v___x_4396_; 
lean_dec_ref_known(v_a_4381_, 1);
lean_dec_ref_known(v_a_4328_, 1);
v___x_4396_ = lean_box(0);
v___y_4368_ = v___y_4389_;
v___y_4369_ = v___y_4387_;
v___y_4370_ = v___y_4388_;
v___y_4371_ = v___y_4390_;
v___y_4372_ = v___y_4393_;
v___y_4373_ = v___y_4385_;
v___y_4374_ = v___y_4384_;
v___y_4375_ = v___y_4391_;
v___y_4376_ = v___y_4392_;
v___y_4377_ = v___y_4386_;
v___y_4378_ = v___x_4396_;
goto v___jp_4367_;
}
else
{
lean_object* v_val_4397_; lean_object* v_val_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4429_; 
v_val_4397_ = lean_ctor_get(v_a_4328_, 0);
v_val_4398_ = lean_ctor_get(v_a_4381_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_a_4381_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4400_ = v_a_4381_;
v_isShared_4401_ = v_isSharedCheck_4429_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_val_4398_);
lean_dec(v_a_4381_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4429_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v_val_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4428_; 
v_val_4402_ = lean_ctor_get(v_orderedAddInst_x3f_4383_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_orderedAddInst_x3f_4383_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4404_ = v_orderedAddInst_x3f_4383_;
v_isShared_4405_ = v_isSharedCheck_4428_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_val_4402_);
lean_dec(v_orderedAddInst_x3f_4383_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4428_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__20));
lean_inc(v_val_4402_);
lean_inc(v_val_4398_);
lean_inc(v_val_4397_);
lean_inc_ref(v_natModuleInst_3741_);
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3758_, v_base_3740_, v_natModuleInst_3741_, v___x_4406_, v_val_4397_, v_val_4398_, v_val_4402_);
lean_inc_ref(v___x_4407_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 0, v___x_4407_);
v___x_4409_ = v___x_4404_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__22));
lean_inc(v_val_4402_);
lean_inc(v_val_4398_);
lean_inc(v_val_4397_);
lean_inc_ref(v_natModuleInst_3741_);
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3758_, v_base_3740_, v_natModuleInst_3741_, v___x_4410_, v_val_4397_, v_val_4398_, v_val_4402_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 0, v___x_4411_);
v___x_4413_ = v___x_4400_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__24));
lean_inc_n(v_val_4402_, 2);
lean_inc(v_val_4398_);
lean_inc_n(v_val_4397_, 3);
lean_inc_ref_n(v_natModuleInst_3741_, 2);
lean_inc_ref_n(v_base_3740_, 2);
lean_inc_n(v_val_3758_, 3);
v___x_4415_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3758_, v_base_3740_, v_natModuleInst_3741_, v___x_4414_, v_val_4397_, v_val_4398_, v_val_4402_);
v___x_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
v___x_4417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__26));
v___x_4418_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3758_, v_base_3740_, v_natModuleInst_3741_, v___x_4417_, v_val_4397_, v_val_4398_, v_val_4402_);
v___x_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
v___x_4420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__30));
v___x_4421_ = lean_box(0);
v___x_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_val_3758_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = l_Lean_mkConst(v___x_4420_, v___x_4422_);
lean_inc_ref(v_type_3739_);
v___x_4424_ = l_Lean_mkAppB(v___x_4423_, v_type_3739_, v___x_4407_);
v___x_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
v___y_4330_ = v___x_4419_;
v___y_4331_ = v___y_4389_;
v___y_4332_ = v___y_4387_;
v___y_4333_ = v___y_4388_;
v___y_4334_ = v___x_4409_;
v___y_4335_ = v___y_4385_;
v___y_4336_ = v___y_4384_;
v___y_4337_ = v___y_4392_;
v___y_4338_ = v___y_4386_;
v_fst_4339_ = v_val_4397_;
v_snd_4340_ = v_val_4402_;
v___y_4341_ = v___x_4416_;
v___y_4342_ = v___y_4390_;
v___y_4343_ = v___y_4393_;
v___y_4344_ = v___x_4413_;
v___y_4345_ = v___y_4391_;
v___y_4346_ = v___x_4425_;
goto v___jp_4329_;
}
}
}
}
}
}
}
}
v___jp_4430_:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_box(0);
v_orderedAddInst_x3f_4383_ = v___x_4441_;
v___y_4384_ = v___y_4431_;
v___y_4385_ = v___y_4432_;
v___y_4386_ = v___y_4433_;
v___y_4387_ = v___y_4434_;
v___y_4388_ = v___y_4435_;
v___y_4389_ = v___y_4436_;
v___y_4390_ = v___y_4437_;
v___y_4391_ = v___y_4438_;
v___y_4392_ = v___y_4439_;
v___y_4393_ = v___y_4440_;
goto v___jp_4382_;
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_a_4328_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4470_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4380_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4380_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
v___jp_4329_:
{
lean_object* v___x_4347_; 
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4347_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_val_3758_, v_base_3740_, v_a_4328_, v___y_4333_, v___y_4331_, v___y_4342_, v___y_4345_, v___y_4337_, v___y_4343_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
if (lean_obj_tag(v_a_4348_) == 0)
{
lean_dec_ref(v_snd_4340_);
lean_dec_ref(v_fst_4339_);
v___y_4254_ = v___y_4330_;
v___y_4255_ = v___y_4341_;
v___y_4256_ = v___y_4344_;
v___y_4257_ = v___y_4334_;
v___y_4258_ = v___y_4346_;
v_isLinearInstQ_x3f_4259_ = v_a_4348_;
v___y_4260_ = v___y_4336_;
v___y_4261_ = v___y_4335_;
v___y_4262_ = v___y_4338_;
v___y_4263_ = v___y_4332_;
v___y_4264_ = v___y_4333_;
v___y_4265_ = v___y_4331_;
v___y_4266_ = v___y_4342_;
v___y_4267_ = v___y_4345_;
v___y_4268_ = v___y_4337_;
v___y_4269_ = v___y_4343_;
goto v___jp_4253_;
}
else
{
lean_object* v_val_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4358_; 
v_val_4349_ = lean_ctor_get(v_a_4348_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v_a_4348_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4351_ = v_a_4348_;
v_isShared_4352_ = v_isSharedCheck_4358_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_val_4349_);
lean_dec(v_a_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4358_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__18));
lean_inc_ref(v_natModuleInst_3741_);
lean_inc_ref(v_base_3740_);
lean_inc(v_val_3758_);
v___x_4354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___lam__1(v_val_3758_, v_base_3740_, v_natModuleInst_3741_, v___x_4353_, v_fst_4339_, v_val_4349_, v_snd_4340_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v___x_4354_);
v___x_4356_ = v___x_4351_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
v___y_4254_ = v___y_4330_;
v___y_4255_ = v___y_4341_;
v___y_4256_ = v___y_4344_;
v___y_4257_ = v___y_4334_;
v___y_4258_ = v___y_4346_;
v_isLinearInstQ_x3f_4259_ = v___x_4356_;
v___y_4260_ = v___y_4336_;
v___y_4261_ = v___y_4335_;
v___y_4262_ = v___y_4338_;
v___y_4263_ = v___y_4332_;
v___y_4264_ = v___y_4333_;
v___y_4265_ = v___y_4331_;
v___y_4266_ = v___y_4342_;
v___y_4267_ = v___y_4345_;
v___y_4268_ = v___y_4337_;
v___y_4269_ = v___y_4343_;
goto v___jp_4253_;
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v___y_4346_);
lean_dec(v___y_4344_);
lean_dec(v___y_4341_);
lean_dec_ref(v_snd_4340_);
lean_dec_ref(v_fst_4339_);
lean_dec(v___y_4334_);
lean_dec(v___y_4330_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4359_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4347_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4347_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
v___jp_4367_:
{
lean_object* v___x_4379_; 
v___x_4379_ = lean_box(0);
v___y_4254_ = v___x_4379_;
v___y_4255_ = v___x_4379_;
v___y_4256_ = v___x_4379_;
v___y_4257_ = v___x_4379_;
v___y_4258_ = v___x_4379_;
v_isLinearInstQ_x3f_4259_ = v___x_4379_;
v___y_4260_ = v___y_4374_;
v___y_4261_ = v___y_4373_;
v___y_4262_ = v___y_4377_;
v___y_4263_ = v___y_4369_;
v___y_4264_ = v___y_4370_;
v___y_4265_ = v___y_4368_;
v___y_4266_ = v___y_4371_;
v___y_4267_ = v___y_4375_;
v___y_4268_ = v___y_4376_;
v___y_4269_ = v___y_4372_;
goto v___jp_4253_;
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4478_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4327_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4327_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
v___jp_3762_:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_3772_, v___y_3768_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v_structs_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v_structs_3785_ = lean_ctor_get(v_a_3784_, 0);
lean_inc_ref(v_structs_3785_);
lean_dec(v_a_3784_);
v___x_3786_ = lean_array_get_size(v_structs_3785_);
lean_dec_ref(v_structs_3785_);
v___x_3787_ = lean_box(0);
lean_inc_ref(v___y_3779_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 0, v___y_3779_);
v___x_3789_ = v___x_3760_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___y_3779_);
v___x_3789_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___f_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_inc_ref(v___y_3763_);
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___y_3763_);
v___x_3791_ = lean_unsigned_to_nat(32u);
v___x_3792_ = lean_mk_empty_array_with_capacity(v___x_3791_);
v___x_3793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__4);
v___x_3794_ = ((size_t)5ULL);
lean_inc(v___y_3765_);
v___x_3795_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3792_);
lean_ctor_set(v___x_3795_, 2, v___y_3765_);
lean_ctor_set(v___x_3795_, 3, v___y_3765_);
lean_ctor_set_usize(v___x_3795_, 4, v___x_3794_);
v___x_3796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__6);
v___x_3797_ = 0;
v___x_3798_ = lean_box(0);
lean_inc_ref_n(v___x_3795_, 7);
v___x_3799_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_3799_, 0, v___x_3786_);
lean_ctor_set(v___x_3799_, 1, v___x_3787_);
lean_ctor_set(v___x_3799_, 2, v_type_3739_);
lean_ctor_set(v___x_3799_, 3, v_val_3758_);
lean_ctor_set(v___x_3799_, 4, v___y_3773_);
lean_ctor_set(v___x_3799_, 5, v___y_3767_);
lean_ctor_set(v___x_3799_, 6, v___y_3778_);
lean_ctor_set(v___x_3799_, 7, v___y_3780_);
lean_ctor_set(v___x_3799_, 8, v___y_3777_);
lean_ctor_set(v___x_3799_, 9, v___y_3764_);
lean_ctor_set(v___x_3799_, 10, v___y_3776_);
lean_ctor_set(v___x_3799_, 11, v___y_3769_);
lean_ctor_set(v___x_3799_, 12, v___x_3787_);
lean_ctor_set(v___x_3799_, 13, v___x_3787_);
lean_ctor_set(v___x_3799_, 14, v___x_3787_);
lean_ctor_set(v___x_3799_, 15, v___x_3787_);
lean_ctor_set(v___x_3799_, 16, v___x_3787_);
lean_ctor_set(v___x_3799_, 17, v___y_3781_);
lean_ctor_set(v___x_3799_, 18, v___y_3766_);
lean_ctor_set(v___x_3799_, 19, v___x_3787_);
lean_ctor_set(v___x_3799_, 20, v___y_3771_);
lean_ctor_set(v___x_3799_, 21, v_a_3782_);
lean_ctor_set(v___x_3799_, 22, v___y_3774_);
lean_ctor_set(v___x_3799_, 23, v___y_3779_);
lean_ctor_set(v___x_3799_, 24, v___y_3763_);
lean_ctor_set(v___x_3799_, 25, v___x_3789_);
lean_ctor_set(v___x_3799_, 26, v___x_3790_);
lean_ctor_set(v___x_3799_, 27, v___x_3787_);
lean_ctor_set(v___x_3799_, 28, v___y_3770_);
lean_ctor_set(v___x_3799_, 29, v___y_3775_);
lean_ctor_set(v___x_3799_, 30, v___x_3795_);
lean_ctor_set(v___x_3799_, 31, v___x_3796_);
lean_ctor_set(v___x_3799_, 32, v___x_3795_);
lean_ctor_set(v___x_3799_, 33, v___x_3795_);
lean_ctor_set(v___x_3799_, 34, v___x_3795_);
lean_ctor_set(v___x_3799_, 35, v___x_3795_);
lean_ctor_set(v___x_3799_, 36, v___x_3787_);
lean_ctor_set(v___x_3799_, 37, v___x_3796_);
lean_ctor_set(v___x_3799_, 38, v___x_3795_);
lean_ctor_set(v___x_3799_, 39, v___x_3798_);
lean_ctor_set(v___x_3799_, 40, v___x_3795_);
lean_ctor_set(v___x_3799_, 41, v___x_3795_);
lean_ctor_set_uint8(v___x_3799_, sizeof(void*)*42, v___x_3797_);
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_3800_, 0, v___x_3799_);
v___x_3801_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_3802_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3801_, v___f_3800_, v___y_3772_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3810_; 
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v___x_3802_, 0);
lean_dec(v_unused_3811_);
v___x_3804_ = v___x_3802_;
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v___x_3802_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3786_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3806_);
v___x_3808_ = v___x_3804_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_a_3812_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3802_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3802_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v_a_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3821_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3783_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3783_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
v___jp_3829_:
{
if (lean_obj_tag(v___y_3848_) == 0)
{
lean_dec(v___y_3851_);
v___y_3763_ = v___y_3830_;
v___y_3764_ = v___y_3831_;
v___y_3765_ = v___y_3833_;
v___y_3766_ = v___y_3835_;
v___y_3767_ = v___y_3837_;
v___y_3768_ = v___y_3838_;
v___y_3769_ = v___y_3839_;
v___y_3770_ = v___y_3841_;
v___y_3771_ = v_a_3854_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3843_;
v___y_3774_ = v___y_3844_;
v___y_3775_ = v___y_3845_;
v___y_3776_ = v___y_3846_;
v___y_3777_ = v___y_3847_;
v___y_3778_ = v___y_3848_;
v___y_3779_ = v___y_3849_;
v___y_3780_ = v___y_3850_;
v___y_3781_ = v___y_3853_;
v_a_3782_ = v___y_3848_;
goto v___jp_3762_;
}
else
{
lean_object* v_val_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_val_3855_ = lean_ctor_get(v___y_3848_, 0);
v___x_3856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__12));
v___x_3857_ = l_Lean_mkConst(v___x_3856_, v___y_3851_);
lean_inc(v_val_3855_);
lean_inc_ref(v_type_3739_);
v___x_3858_ = l_Lean_mkAppB(v___x_3857_, v_type_3739_, v_val_3855_);
v___x_3859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3858_, v___y_3852_, v___y_3836_, v___y_3840_, v___y_3832_, v___y_3838_, v___y_3834_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3861_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_a_3860_);
v___y_3763_ = v___y_3830_;
v___y_3764_ = v___y_3831_;
v___y_3765_ = v___y_3833_;
v___y_3766_ = v___y_3835_;
v___y_3767_ = v___y_3837_;
v___y_3768_ = v___y_3838_;
v___y_3769_ = v___y_3839_;
v___y_3770_ = v___y_3841_;
v___y_3771_ = v_a_3854_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3843_;
v___y_3774_ = v___y_3844_;
v___y_3775_ = v___y_3845_;
v___y_3776_ = v___y_3846_;
v___y_3777_ = v___y_3847_;
v___y_3778_ = v___y_3848_;
v___y_3779_ = v___y_3849_;
v___y_3780_ = v___y_3850_;
v___y_3781_ = v___y_3853_;
v_a_3782_ = v___x_3861_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref_known(v___y_3848_, 1);
lean_dec(v_a_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3839_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3862_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3859_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3859_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
v___jp_3870_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__15));
lean_inc_ref(v___y_3873_);
v___x_3910_ = l_Lean_Name_mkStr2(v___y_3873_, v___x_3909_);
lean_inc(v___y_3883_);
v___x_3911_ = l_Lean_mkConst(v___x_3910_, v___y_3883_);
lean_inc_ref(v_type_3739_);
v___x_3912_ = l_Lean_mkAppB(v___x_3911_, v_type_3739_, v___y_3885_);
v___x_3913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_3912_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__20));
lean_inc_ref(v___y_3886_);
v___x_3916_ = l_Lean_Name_mkStr2(v___y_3886_, v___x_3915_);
lean_inc(v___y_3883_);
v___x_3917_ = l_Lean_mkConst(v___x_3916_, v___y_3883_);
lean_inc_ref(v_type_3739_);
v___x_3918_ = l_Lean_mkApp3(v___x_3917_, v_type_3739_, v___y_3895_, v___y_3882_);
v___x_3919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3918_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__63));
lean_inc_ref(v___y_3898_);
v___x_3922_ = l_Lean_Name_mkStr2(v___y_3898_, v___x_3921_);
lean_inc(v___y_3897_);
v___x_3923_ = l_Lean_mkConst(v___x_3922_, v___y_3897_);
lean_inc_ref_n(v_type_3739_, 3);
v___x_3924_ = l_Lean_mkApp4(v___x_3923_, v_type_3739_, v_type_3739_, v_type_3739_, v___y_3892_);
v___x_3925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3924_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__24));
lean_inc_ref(v___y_3875_);
v___x_3928_ = l_Lean_Name_mkStr2(v___y_3875_, v___x_3927_);
v___x_3929_ = l_Lean_mkConst(v___x_3928_, v___y_3897_);
lean_inc_ref_n(v_type_3739_, 3);
v___x_3930_ = l_Lean_mkApp4(v___x_3929_, v_type_3739_, v_type_3739_, v_type_3739_, v___y_3896_);
v___x_3931_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3930_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__28));
lean_inc_ref(v___y_3876_);
v___x_3934_ = l_Lean_Name_mkStr2(v___y_3876_, v___x_3933_);
lean_inc(v___y_3883_);
v___x_3935_ = l_Lean_mkConst(v___x_3934_, v___y_3883_);
lean_inc_ref(v_type_3739_);
v___x_3936_ = l_Lean_mkAppB(v___x_3935_, v_type_3739_, v___y_3880_);
v___x_3937_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3936_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__0));
lean_inc_ref(v___y_3889_);
v___x_3940_ = l_Lean_Name_mkStr2(v___y_3889_, v___x_3939_);
v___x_3941_ = l_Lean_mkConst(v___x_3940_, v___y_3877_);
lean_inc_ref_n(v_type_3739_, 2);
lean_inc_ref(v___x_3941_);
v___x_3942_ = l_Lean_mkApp4(v___x_3941_, v___y_3888_, v_type_3739_, v_type_3739_, v___y_3884_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3942_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
lean_inc_ref_n(v_type_3739_, 2);
v___x_3945_ = l_Lean_mkApp4(v___x_3941_, v___y_3893_, v_type_3739_, v_type_3739_, v___y_3894_);
v___x_3946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3945_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3946_) == 0)
{
if (lean_obj_tag(v___y_3887_) == 0)
{
lean_object* v_a_3947_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v___y_3830_ = v_a_3947_;
v___y_3831_ = v___y_3871_;
v___y_3832_ = v___y_3906_;
v___y_3833_ = v___y_3872_;
v___y_3834_ = v___y_3908_;
v___y_3835_ = v_a_3920_;
v___y_3836_ = v___y_3904_;
v___y_3837_ = v___y_3887_;
v___y_3838_ = v___y_3907_;
v___y_3839_ = v___y_3874_;
v___y_3840_ = v___y_3905_;
v___y_3841_ = v_a_3932_;
v___y_3842_ = v___y_3899_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v_a_3926_;
v___y_3845_ = v_a_3938_;
v___y_3846_ = v___y_3890_;
v___y_3847_ = v___y_3879_;
v___y_3848_ = v___y_3891_;
v___y_3849_ = v_a_3944_;
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3883_;
v___y_3852_ = v___y_3903_;
v___y_3853_ = v_a_3914_;
v_a_3854_ = v___y_3887_;
goto v___jp_3829_;
}
else
{
lean_object* v_a_3948_; lean_object* v_val_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_a_3948_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3946_, 1);
v_val_3949_ = lean_ctor_get(v___y_3887_, 0);
v___x_3950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__46));
lean_inc(v___y_3883_);
v___x_3951_ = l_Lean_mkConst(v___x_3950_, v___y_3883_);
lean_inc(v_val_3949_);
lean_inc_ref(v_type_3739_);
v___x_3952_ = l_Lean_mkAppB(v___x_3951_, v_type_3739_, v_val_3949_);
v___x_3953_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_3952_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_a_3954_);
v___y_3830_ = v_a_3948_;
v___y_3831_ = v___y_3871_;
v___y_3832_ = v___y_3906_;
v___y_3833_ = v___y_3872_;
v___y_3834_ = v___y_3908_;
v___y_3835_ = v_a_3920_;
v___y_3836_ = v___y_3904_;
v___y_3837_ = v___y_3887_;
v___y_3838_ = v___y_3907_;
v___y_3839_ = v___y_3874_;
v___y_3840_ = v___y_3905_;
v___y_3841_ = v_a_3932_;
v___y_3842_ = v___y_3899_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v_a_3926_;
v___y_3845_ = v_a_3938_;
v___y_3846_ = v___y_3890_;
v___y_3847_ = v___y_3879_;
v___y_3848_ = v___y_3891_;
v___y_3849_ = v_a_3944_;
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3883_;
v___y_3852_ = v___y_3903_;
v___y_3853_ = v_a_3914_;
v_a_3854_ = v___x_3955_;
goto v___jp_3829_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_a_3948_);
lean_dec_ref_known(v___y_3887_, 1);
lean_dec(v_a_3944_);
lean_dec(v_a_3938_);
lean_dec(v_a_3932_);
lean_dec(v_a_3926_);
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3956_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3953_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3953_);
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
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_a_3944_);
lean_dec(v_a_3938_);
lean_dec(v_a_3932_);
lean_dec(v_a_3926_);
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v___y_3887_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3964_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3946_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3946_);
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
lean_dec_ref(v___x_3941_);
lean_dec(v_a_3938_);
lean_dec(v_a_3932_);
lean_dec(v_a_3926_);
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v___y_3887_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3972_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3943_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3943_);
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
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3932_);
lean_dec(v_a_3926_);
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3980_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3937_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3937_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3926_);
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3988_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3931_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3931_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v_a_3920_);
lean_dec(v_a_3914_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_3996_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3925_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3925_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec(v_a_3914_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4004_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3919_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3919_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4012_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3913_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3913_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
v___jp_4020_:
{
if (lean_obj_tag(v___y_4041_) == 1)
{
lean_object* v_val_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_val_4059_ = lean_ctor_get(v___y_4041_, 0);
v___x_4060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc(v___y_4032_);
v___x_4061_ = l_Lean_mkConst(v___x_4060_, v___y_4032_);
lean_inc_ref(v_type_3739_);
v___x_4062_ = l_Lean_Expr_app___override(v___x_4061_, v_type_3739_);
lean_inc(v_val_4059_);
v___x_4063_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4062_, v_val_4059_, v___y_4054_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_dec_ref_known(v___x_4063_, 1);
v___y_3871_ = v___y_4021_;
v___y_3872_ = v___y_4022_;
v___y_3873_ = v___y_4023_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4028_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4026_;
v___y_3879_ = v___y_4029_;
v___y_3880_ = v___y_4030_;
v___y_3881_ = v___y_4031_;
v___y_3882_ = v___y_4033_;
v___y_3883_ = v___y_4032_;
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
v___y_3896_ = v___y_4048_;
v___y_3897_ = v___y_4047_;
v___y_3898_ = v___y_4046_;
v___y_3899_ = v___y_4049_;
v___y_3900_ = v___y_4050_;
v___y_3901_ = v___y_4051_;
v___y_3902_ = v___y_4052_;
v___y_3903_ = v___y_4053_;
v___y_3904_ = v___y_4054_;
v___y_3905_ = v___y_4055_;
v___y_3906_ = v___y_4056_;
v___y_3907_ = v___y_4057_;
v___y_3908_ = v___y_4058_;
goto v___jp_3870_;
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec_ref_known(v___y_4041_, 1);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4024_);
lean_dec(v___y_4022_);
lean_dec(v___y_4021_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
else
{
v___y_3871_ = v___y_4021_;
v___y_3872_ = v___y_4022_;
v___y_3873_ = v___y_4023_;
v___y_3874_ = v___y_4024_;
v___y_3875_ = v___y_4025_;
v___y_3876_ = v___y_4028_;
v___y_3877_ = v___y_4027_;
v___y_3878_ = v___y_4026_;
v___y_3879_ = v___y_4029_;
v___y_3880_ = v___y_4030_;
v___y_3881_ = v___y_4031_;
v___y_3882_ = v___y_4033_;
v___y_3883_ = v___y_4032_;
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
v___y_3896_ = v___y_4048_;
v___y_3897_ = v___y_4047_;
v___y_3898_ = v___y_4046_;
v___y_3899_ = v___y_4049_;
v___y_3900_ = v___y_4050_;
v___y_3901_ = v___y_4051_;
v___y_3902_ = v___y_4052_;
v___y_3903_ = v___y_4053_;
v___y_3904_ = v___y_4054_;
v___y_3905_ = v___y_4055_;
v___y_3906_ = v___y_4056_;
v___y_3907_ = v___y_4057_;
v___y_3908_ = v___y_4058_;
goto v___jp_3870_;
}
}
v___jp_4073_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__2));
lean_inc_n(v___y_4080_, 14);
v___x_4093_ = l_Lean_mkConst(v___x_4092_, v___y_4080_);
v___x_4094_ = l_Lean_mkAppB(v___x_4093_, v_base_3740_, v_natModuleInst_3741_);
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__55));
v___x_4096_ = l_Lean_mkConst(v___x_4095_, v___y_4080_);
lean_inc_ref_n(v___x_4094_, 4);
lean_inc_ref_n(v_type_3739_, 14);
v___x_4097_ = l_Lean_mkAppB(v___x_4096_, v_type_3739_, v___x_4094_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__58));
v___x_4099_ = l_Lean_mkConst(v___x_4098_, v___y_4080_);
lean_inc_ref_n(v___x_4097_, 2);
v___x_4100_ = l_Lean_mkAppB(v___x_4099_, v_type_3739_, v___x_4097_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__3));
v___x_4102_ = l_Lean_mkConst(v___x_4101_, v___y_4080_);
lean_inc_ref(v___x_4100_);
v___x_4103_ = l_Lean_mkAppB(v___x_4102_, v_type_3739_, v___x_4100_);
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__13));
v___x_4105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__5));
v___x_4106_ = l_Lean_mkConst(v___x_4105_, v___y_4080_);
lean_inc_ref(v___x_4103_);
v___x_4107_ = l_Lean_mkAppB(v___x_4106_, v_type_3739_, v___x_4103_);
v___x_4108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__34));
v___x_4109_ = l_Lean_mkConst(v___x_4108_, v___y_4080_);
v___x_4110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__6));
v___x_4111_ = l_Lean_mkConst(v___x_4110_, v___y_4080_);
v___x_4112_ = l_Lean_mkAppB(v___x_4111_, v_type_3739_, v___x_4100_);
v___x_4113_ = l_Lean_mkAppB(v___x_4109_, v_type_3739_, v___x_4112_);
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__37));
v___x_4115_ = l_Lean_mkConst(v___x_4114_, v___y_4080_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__7));
v___x_4117_ = l_Lean_mkConst(v___x_4116_, v___y_4080_);
v___x_4118_ = l_Lean_mkAppB(v___x_4117_, v_type_3739_, v___x_4097_);
v___x_4119_ = l_Lean_mkAppB(v___x_4115_, v_type_3739_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__8));
v___x_4121_ = l_Lean_mkConst(v___x_4120_, v___y_4080_);
v___x_4122_ = l_Lean_mkAppB(v___x_4121_, v_type_3739_, v___x_4097_);
v___x_4123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__41));
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
lean_ctor_set(v___x_4126_, 1, v___y_4080_);
v___x_4127_ = l_Lean_mkConst(v___x_4123_, v___x_4126_);
v___x_4128_ = l_Lean_Int_mkType;
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__9));
v___x_4130_ = l_Lean_mkConst(v___x_4129_, v___y_4080_);
v___x_4131_ = l_Lean_mkAppB(v___x_4130_, v_type_3739_, v___x_4094_);
lean_inc_ref(v___x_4127_);
v___x_4132_ = l_Lean_mkApp3(v___x_4127_, v___x_4128_, v_type_3739_, v___x_4131_);
v___x_4133_ = l_Lean_Nat_mkType;
v___x_4134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__10));
v___x_4135_ = l_Lean_mkConst(v___x_4134_, v___y_4080_);
v___x_4136_ = l_Lean_mkAppB(v___x_4135_, v_type_3739_, v___x_4094_);
v___x_4137_ = l_Lean_mkApp3(v___x_4127_, v___x_4133_, v_type_3739_, v___x_4136_);
v___x_4138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkIntModuleInst_x3f___redArg___closed__3));
v___x_4139_ = l_Lean_mkConst(v___x_4138_, v___y_4080_);
v___x_4140_ = l_Lean_Expr_app___override(v___x_4139_, v_type_3739_);
v___x_4141_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4140_, v___x_4094_, v___y_4087_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_dec_ref_known(v___x_4141_, 1);
v___x_4142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc(v___y_4080_);
v___x_4143_ = l_Lean_mkConst(v___x_4142_, v___y_4080_);
lean_inc_ref(v_type_3739_);
v___x_4144_ = l_Lean_Expr_app___override(v___x_4143_, v_type_3739_);
lean_inc_ref(v___x_4103_);
v___x_4145_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4144_, v___x_4103_, v___y_4087_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_dec_ref_known(v___x_4145_, 1);
v___x_4146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__17));
v___x_4147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__18));
lean_inc(v___y_4080_);
v___x_4148_ = l_Lean_mkConst(v___x_4147_, v___y_4080_);
v___x_4149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__19);
lean_inc_ref(v_type_3739_);
v___x_4150_ = l_Lean_mkAppB(v___x_4148_, v_type_3739_, v___x_4149_);
lean_inc_ref(v___x_4107_);
v___x_4151_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4150_, v___x_4107_, v___y_4087_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec_ref_known(v___x_4151_, 1);
v___x_4152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__61));
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc(v___y_4080_);
lean_inc_n(v_val_3758_, 2);
v___x_4154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4154_, 0, v_val_3758_);
lean_ctor_set(v___x_4154_, 1, v___y_4080_);
lean_inc_ref(v___x_4154_);
v___x_4155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4155_, 0, v_val_3758_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
lean_inc_ref(v___x_4155_);
v___x_4156_ = l_Lean_mkConst(v___x_4153_, v___x_4155_);
lean_inc_ref_n(v_type_3739_, 3);
v___x_4157_ = l_Lean_mkApp3(v___x_4156_, v_type_3739_, v_type_3739_, v_type_3739_);
lean_inc_ref(v___x_4113_);
v___x_4158_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4157_, v___x_4113_, v___y_4087_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref_known(v___x_4158_, 1);
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__22));
v___x_4160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__23));
lean_inc_ref(v___x_4155_);
v___x_4161_ = l_Lean_mkConst(v___x_4160_, v___x_4155_);
lean_inc_ref_n(v_type_3739_, 3);
v___x_4162_ = l_Lean_mkApp3(v___x_4161_, v_type_3739_, v_type_3739_, v_type_3739_);
lean_inc_ref(v___x_4119_);
v___x_4163_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4162_, v___x_4119_, v___y_4087_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec_ref_known(v___x_4163_, 1);
v___x_4164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__26));
v___x_4165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__27));
lean_inc(v___y_4080_);
v___x_4166_ = l_Lean_mkConst(v___x_4165_, v___y_4080_);
lean_inc_ref(v_type_3739_);
v___x_4167_ = l_Lean_Expr_app___override(v___x_4166_, v_type_3739_);
lean_inc_ref(v___x_4122_);
v___x_4168_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4167_, v___x_4122_, v___y_4087_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec_ref_known(v___x_4168_, 1);
v___x_4169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__0));
v___x_4170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__1));
v___x_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4125_);
lean_ctor_set(v___x_4171_, 1, v___x_4154_);
lean_inc_ref(v___x_4171_);
v___x_4172_ = l_Lean_mkConst(v___x_4170_, v___x_4171_);
lean_inc_ref_n(v_type_3739_, 2);
lean_inc_ref(v___x_4172_);
v___x_4173_ = l_Lean_mkApp3(v___x_4172_, v___x_4128_, v_type_3739_, v_type_3739_);
lean_inc_ref(v___x_4132_);
v___x_4174_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4173_, v___x_4132_, v___y_4087_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec_ref_known(v___x_4174_, 1);
lean_inc_ref_n(v_type_3739_, 2);
v___x_4175_ = l_Lean_mkApp3(v___x_4172_, v___x_4133_, v_type_3739_, v_type_3739_);
lean_inc_ref(v___x_4137_);
v___x_4176_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4175_, v___x_4137_, v___y_4087_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_dec_ref_known(v___x_4176_, 1);
if (lean_obj_tag(v___y_4078_) == 1)
{
lean_object* v_val_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v_val_4177_ = lean_ctor_get(v___y_4078_, 0);
lean_inc(v___y_4080_);
v___x_4178_ = l_Lean_mkConst(v___x_4072_, v___y_4080_);
lean_inc_ref(v_type_3739_);
v___x_4179_ = l_Lean_Expr_app___override(v___x_4178_, v_type_3739_);
lean_inc(v_val_4177_);
v___x_4180_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_4179_, v_val_4177_, v___y_4087_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_dec_ref_known(v___x_4180_, 1);
v___y_4021_ = v___y_4075_;
v___y_4022_ = v___x_4124_;
v___y_4023_ = v___x_4104_;
v___y_4024_ = v_noNatDivInstQ_x3f_4081_;
v___y_4025_ = v___x_4159_;
v___y_4026_ = v___x_4094_;
v___y_4027_ = v___x_4171_;
v___y_4028_ = v___x_4164_;
v___y_4029_ = v___y_4076_;
v___y_4030_ = v___x_4122_;
v___y_4031_ = v___y_4079_;
v___y_4032_ = v___y_4080_;
v___y_4033_ = v___x_4107_;
v___y_4034_ = v___x_4132_;
v___y_4035_ = v___x_4103_;
v___y_4036_ = v___x_4146_;
v___y_4037_ = v___y_4078_;
v___y_4038_ = v___x_4128_;
v___y_4039_ = v___x_4169_;
v___y_4040_ = v___y_4074_;
v___y_4041_ = v___y_4077_;
v___y_4042_ = v___x_4113_;
v___y_4043_ = v___x_4133_;
v___y_4044_ = v___x_4137_;
v___y_4045_ = v___x_4149_;
v___y_4046_ = v___x_4152_;
v___y_4047_ = v___x_4155_;
v___y_4048_ = v___x_4119_;
v___y_4049_ = v___y_4082_;
v___y_4050_ = v___y_4083_;
v___y_4051_ = v___y_4084_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4086_;
v___y_4054_ = v___y_4087_;
v___y_4055_ = v___y_4088_;
v___y_4056_ = v___y_4089_;
v___y_4057_ = v___y_4090_;
v___y_4058_ = v___y_4091_;
goto v___jp_4020_;
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref_known(v___y_4078_, 1);
lean_dec_ref_known(v___x_4171_, 2);
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4180_);
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
v___y_4021_ = v___y_4075_;
v___y_4022_ = v___x_4124_;
v___y_4023_ = v___x_4104_;
v___y_4024_ = v_noNatDivInstQ_x3f_4081_;
v___y_4025_ = v___x_4159_;
v___y_4026_ = v___x_4094_;
v___y_4027_ = v___x_4171_;
v___y_4028_ = v___x_4164_;
v___y_4029_ = v___y_4076_;
v___y_4030_ = v___x_4122_;
v___y_4031_ = v___y_4079_;
v___y_4032_ = v___y_4080_;
v___y_4033_ = v___x_4107_;
v___y_4034_ = v___x_4132_;
v___y_4035_ = v___x_4103_;
v___y_4036_ = v___x_4146_;
v___y_4037_ = v___y_4078_;
v___y_4038_ = v___x_4128_;
v___y_4039_ = v___x_4169_;
v___y_4040_ = v___y_4074_;
v___y_4041_ = v___y_4077_;
v___y_4042_ = v___x_4113_;
v___y_4043_ = v___x_4133_;
v___y_4044_ = v___x_4137_;
v___y_4045_ = v___x_4149_;
v___y_4046_ = v___x_4152_;
v___y_4047_ = v___x_4155_;
v___y_4048_ = v___x_4119_;
v___y_4049_ = v___y_4082_;
v___y_4050_ = v___y_4083_;
v___y_4051_ = v___y_4084_;
v___y_4052_ = v___y_4085_;
v___y_4053_ = v___y_4086_;
v___y_4054_ = v___y_4087_;
v___y_4055_ = v___y_4088_;
v___y_4056_ = v___y_4089_;
v___y_4057_ = v___y_4090_;
v___y_4058_ = v___y_4091_;
goto v___jp_4020_;
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref_known(v___x_4171_, 2);
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4189_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4176_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4176_);
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
lean_dec_ref(v___x_4172_);
lean_dec_ref_known(v___x_4171_, 2);
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4197_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4174_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4174_);
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
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref_known(v___x_4154_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4205_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4168_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4168_);
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
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref_known(v___x_4154_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4213_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4163_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4163_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref_known(v___x_4155_, 2);
lean_dec_ref_known(v___x_4154_, 2);
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4221_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4158_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4158_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4229_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4151_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4151_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4237_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4145_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4145_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref(v___x_4137_);
lean_dec_ref(v___x_4132_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4113_);
lean_dec_ref(v___x_4107_);
lean_dec_ref(v___x_4103_);
lean_dec_ref(v___x_4094_);
lean_dec(v_noNatDivInstQ_x3f_4081_);
lean_dec(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_type_3739_);
v_a_4245_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4141_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4141_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
v___jp_4253_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
v___x_4271_ = lean_box(0);
lean_inc(v_val_3758_);
v___x_4272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4272_, 0, v_val_3758_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
lean_inc_ref(v___x_4272_);
v___x_4273_ = l_Lean_mkConst(v___x_4270_, v___x_4272_);
lean_inc_ref(v_base_3740_);
v___x_4274_ = l_Lean_Expr_app___override(v___x_4273_, v_base_3740_);
v___x_4275_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4274_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
if (lean_obj_tag(v_a_4276_) == 1)
{
lean_object* v_val_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_val_4277_ = lean_ctor_get(v_a_4276_, 0);
lean_inc(v_val_4277_);
lean_dec_ref_known(v_a_4276_, 1);
v___x_4278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4272_);
v___x_4279_ = l_Lean_mkConst(v___x_4278_, v___x_4272_);
lean_inc_ref(v_base_3740_);
v___x_4280_ = l_Lean_mkAppB(v___x_4279_, v_base_3740_, v_val_4277_);
v___x_4281_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4280_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
if (lean_obj_tag(v_a_4282_) == 1)
{
lean_object* v_val_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_val_4283_ = lean_ctor_get(v_a_4282_, 0);
lean_inc(v_val_4283_);
lean_dec_ref_known(v_a_4282_, 1);
v___x_4284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__3));
lean_inc_ref(v___x_4272_);
v___x_4285_ = l_Lean_mkConst(v___x_4284_, v___x_4272_);
lean_inc_ref(v_natModuleInst_3741_);
lean_inc_ref(v_base_3740_);
v___x_4286_ = l_Lean_mkAppB(v___x_4285_, v_base_3740_, v_natModuleInst_3741_);
v___x_4287_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4286_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
if (lean_obj_tag(v_a_4288_) == 1)
{
lean_object* v_val_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4299_; 
v_val_4289_ = lean_ctor_get(v_a_4288_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_a_4288_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4291_ = v_a_4288_;
v_isShared_4292_ = v_isSharedCheck_4299_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_val_4289_);
lean_dec(v_a_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4299_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__16));
lean_inc_ref(v___x_4272_);
v___x_4294_ = l_Lean_mkConst(v___x_4293_, v___x_4272_);
lean_inc_ref(v_natModuleInst_3741_);
lean_inc_ref(v_base_3740_);
v___x_4295_ = l_Lean_mkApp4(v___x_4294_, v_base_3740_, v_natModuleInst_3741_, v_val_4283_, v_val_4289_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4295_);
v___x_4297_ = v___x_4291_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
v___y_4074_ = v_isLinearInstQ_x3f_4259_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___y_4255_;
v___y_4077_ = v___y_4256_;
v___y_4078_ = v___y_4257_;
v___y_4079_ = v___y_4258_;
v___y_4080_ = v___x_4272_;
v_noNatDivInstQ_x3f_4081_ = v___x_4297_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
v___y_4090_ = v___y_4268_;
v___y_4091_ = v___y_4269_;
goto v___jp_4073_;
}
}
}
else
{
lean_object* v___x_4300_; 
lean_dec(v_a_4288_);
lean_dec(v_val_4283_);
v___x_4300_ = lean_box(0);
v___y_4074_ = v_isLinearInstQ_x3f_4259_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___y_4255_;
v___y_4077_ = v___y_4256_;
v___y_4078_ = v___y_4257_;
v___y_4079_ = v___y_4258_;
v___y_4080_ = v___x_4272_;
v_noNatDivInstQ_x3f_4081_ = v___x_4300_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
v___y_4090_ = v___y_4268_;
v___y_4091_ = v___y_4269_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_val_4283_);
lean_dec_ref_known(v___x_4272_, 2);
lean_dec(v_isLinearInstQ_x3f_4259_);
lean_dec(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4301_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4287_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4287_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v___x_4309_; 
lean_dec(v_a_4282_);
v___x_4309_ = lean_box(0);
v___y_4074_ = v_isLinearInstQ_x3f_4259_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___y_4255_;
v___y_4077_ = v___y_4256_;
v___y_4078_ = v___y_4257_;
v___y_4079_ = v___y_4258_;
v___y_4080_ = v___x_4272_;
v_noNatDivInstQ_x3f_4081_ = v___x_4309_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
v___y_4090_ = v___y_4268_;
v___y_4091_ = v___y_4269_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec_ref_known(v___x_4272_, 2);
lean_dec(v_isLinearInstQ_x3f_4259_);
lean_dec(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4310_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4281_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4281_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v___x_4318_; 
lean_dec(v_a_4276_);
v___x_4318_ = lean_box(0);
v___y_4074_ = v_isLinearInstQ_x3f_4259_;
v___y_4075_ = v___y_4254_;
v___y_4076_ = v___y_4255_;
v___y_4077_ = v___y_4256_;
v___y_4078_ = v___y_4257_;
v___y_4079_ = v___y_4258_;
v___y_4080_ = v___x_4272_;
v_noNatDivInstQ_x3f_4081_ = v___x_4318_;
v___y_4082_ = v___y_4260_;
v___y_4083_ = v___y_4261_;
v___y_4084_ = v___y_4262_;
v___y_4085_ = v___y_4263_;
v___y_4086_ = v___y_4264_;
v___y_4087_ = v___y_4265_;
v___y_4088_ = v___y_4266_;
v___y_4089_ = v___y_4267_;
v___y_4090_ = v___y_4268_;
v___y_4091_ = v___y_4269_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref_known(v___x_4272_, 2);
lean_dec(v_isLinearInstQ_x3f_4259_);
lean_dec(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
lean_del_object(v___x_3760_);
lean_dec(v_val_3758_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4319_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4275_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4275_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
lean_dec(v_a_3754_);
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v___x_4487_ = lean_box(0);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v___x_4487_);
v___x_4489_ = v___x_3756_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v_natModuleInst_3741_);
lean_dec_ref(v_base_3740_);
lean_dec_ref(v_type_3739_);
v_a_4492_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_3753_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_3753_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___boxed(lean_object* v_type_4500_, lean_object* v_base_4501_, lean_object* v_natModuleInst_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4500_, v_base_4501_, v_natModuleInst_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(lean_object* v_type_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; 
v___x_4534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4535_ = lean_unsigned_to_nat(2u);
v___x_4536_ = l_Lean_Expr_isAppOfArity(v_type_4522_, v___x_4534_, v___x_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
v___x_4537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f(v_type_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4538_ = l_Lean_Expr_appFn_x21(v_type_4522_);
v___x_4539_ = l_Lean_Expr_appArg_x21(v___x_4538_);
lean_dec_ref(v___x_4538_);
v___x_4540_ = l_Lean_Expr_appArg_x21(v_type_4522_);
v___x_4541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f(v_type_4522_, v___x_4539_, v___x_4540_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___boxed(lean_object* v_type_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec(v_a_4543_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0(lean_object* v_type_4555_, lean_object* v_a_4556_, lean_object* v_s_4557_){
_start:
{
lean_object* v_structs_4558_; lean_object* v_typeIdOf_4559_; lean_object* v_exprToStructId_4560_; lean_object* v_exprToStructIdEntries_4561_; lean_object* v_forbiddenNatModules_4562_; lean_object* v_natStructs_4563_; lean_object* v_natTypeIdOf_4564_; lean_object* v_exprToNatStructId_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4573_; 
v_structs_4558_ = lean_ctor_get(v_s_4557_, 0);
v_typeIdOf_4559_ = lean_ctor_get(v_s_4557_, 1);
v_exprToStructId_4560_ = lean_ctor_get(v_s_4557_, 2);
v_exprToStructIdEntries_4561_ = lean_ctor_get(v_s_4557_, 3);
v_forbiddenNatModules_4562_ = lean_ctor_get(v_s_4557_, 4);
v_natStructs_4563_ = lean_ctor_get(v_s_4557_, 5);
v_natTypeIdOf_4564_ = lean_ctor_get(v_s_4557_, 6);
v_exprToNatStructId_4565_ = lean_ctor_get(v_s_4557_, 7);
v_isSharedCheck_4573_ = !lean_is_exclusive(v_s_4557_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4567_ = v_s_4557_;
v_isShared_4568_ = v_isSharedCheck_4573_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_exprToNatStructId_4565_);
lean_inc(v_natTypeIdOf_4564_);
lean_inc(v_natStructs_4563_);
lean_inc(v_forbiddenNatModules_4562_);
lean_inc(v_exprToStructIdEntries_4561_);
lean_inc(v_exprToStructId_4560_);
lean_inc(v_typeIdOf_4559_);
lean_inc(v_structs_4558_);
lean_dec(v_s_4557_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4573_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4569_; lean_object* v___x_4571_; 
v___x_4569_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_typeIdOf_4559_, v_type_4555_, v_a_4556_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4569_);
v___x_4571_ = v___x_4567_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_structs_4558_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_exprToStructId_4560_);
lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_exprToStructIdEntries_4561_);
lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_forbiddenNatModules_4562_);
lean_ctor_set(v_reuseFailAlloc_4572_, 5, v_natStructs_4563_);
lean_ctor_set(v_reuseFailAlloc_4572_, 6, v_natTypeIdOf_4564_);
lean_ctor_set(v_reuseFailAlloc_4572_, 7, v_exprToNatStructId_4565_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4574_, lean_object* v_vals_4575_, lean_object* v_i_4576_, lean_object* v_k_4577_){
_start:
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = lean_array_get_size(v_keys_4574_);
v___x_4579_ = lean_nat_dec_lt(v_i_4576_, v___x_4578_);
if (v___x_4579_ == 0)
{
lean_object* v___x_4580_; 
lean_dec(v_i_4576_);
v___x_4580_ = lean_box(0);
return v___x_4580_;
}
else
{
lean_object* v_k_x27_4581_; size_t v___x_4582_; size_t v___x_4583_; uint8_t v___x_4584_; 
v_k_x27_4581_ = lean_array_fget_borrowed(v_keys_4574_, v_i_4576_);
v___x_4582_ = lean_ptr_addr(v_k_4577_);
v___x_4583_ = lean_ptr_addr(v_k_x27_4581_);
v___x_4584_ = lean_usize_dec_eq(v___x_4582_, v___x_4583_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_unsigned_to_nat(1u);
v___x_4586_ = lean_nat_add(v_i_4576_, v___x_4585_);
lean_dec(v_i_4576_);
v_i_4576_ = v___x_4586_;
goto _start;
}
else
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = lean_array_fget_borrowed(v_vals_4575_, v_i_4576_);
lean_dec(v_i_4576_);
lean_inc(v___x_4588_);
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4590_, lean_object* v_vals_4591_, lean_object* v_i_4592_, lean_object* v_k_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4590_, v_vals_4591_, v_i_4592_, v_k_4593_);
lean_dec_ref(v_k_4593_);
lean_dec_ref(v_vals_4591_);
lean_dec_ref(v_keys_4590_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_4595_, size_t v_x_4596_, lean_object* v_x_4597_){
_start:
{
if (lean_obj_tag(v_x_4595_) == 0)
{
lean_object* v_es_4598_; lean_object* v___x_4599_; size_t v___x_4600_; size_t v___x_4601_; lean_object* v_j_4602_; lean_object* v___x_4603_; 
v_es_4598_ = lean_ctor_get(v_x_4595_, 0);
v___x_4599_ = lean_box(2);
v___x_4600_ = ((size_t)31ULL);
v___x_4601_ = lean_usize_land(v_x_4596_, v___x_4600_);
v_j_4602_ = lean_usize_to_nat(v___x_4601_);
v___x_4603_ = lean_array_get_borrowed(v___x_4599_, v_es_4598_, v_j_4602_);
lean_dec(v_j_4602_);
switch(lean_obj_tag(v___x_4603_))
{
case 0:
{
lean_object* v_key_4604_; lean_object* v_val_4605_; size_t v___x_4606_; size_t v___x_4607_; uint8_t v___x_4608_; 
v_key_4604_ = lean_ctor_get(v___x_4603_, 0);
v_val_4605_ = lean_ctor_get(v___x_4603_, 1);
v___x_4606_ = lean_ptr_addr(v_x_4597_);
v___x_4607_ = lean_ptr_addr(v_key_4604_);
v___x_4608_ = lean_usize_dec_eq(v___x_4606_, v___x_4607_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; 
v___x_4609_ = lean_box(0);
return v___x_4609_;
}
else
{
lean_object* v___x_4610_; 
lean_inc(v_val_4605_);
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v_val_4605_);
return v___x_4610_;
}
}
case 1:
{
lean_object* v_node_4611_; size_t v___x_4612_; size_t v___x_4613_; 
v_node_4611_ = lean_ctor_get(v___x_4603_, 0);
v___x_4612_ = ((size_t)5ULL);
v___x_4613_ = lean_usize_shift_right(v_x_4596_, v___x_4612_);
v_x_4595_ = v_node_4611_;
v_x_4596_ = v___x_4613_;
goto _start;
}
default: 
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_box(0);
return v___x_4615_;
}
}
}
else
{
lean_object* v_ks_4616_; lean_object* v_vs_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v_ks_4616_ = lean_ctor_get(v_x_4595_, 0);
v_vs_4617_ = lean_ctor_get(v_x_4595_, 1);
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4616_, v_vs_4617_, v___x_4618_, v_x_4597_);
return v___x_4619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_4620_, lean_object* v_x_4621_, lean_object* v_x_4622_){
_start:
{
size_t v_x_6741__boxed_4623_; lean_object* v_res_4624_; 
v_x_6741__boxed_4623_ = lean_unbox_usize(v_x_4621_);
lean_dec(v_x_4621_);
v_res_4624_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4620_, v_x_6741__boxed_4623_, v_x_4622_);
lean_dec_ref(v_x_4622_);
lean_dec_ref(v_x_4620_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(lean_object* v_x_4625_, lean_object* v_x_4626_){
_start:
{
size_t v___x_4627_; size_t v___x_4628_; size_t v___x_4629_; uint64_t v___x_4630_; size_t v___x_4631_; lean_object* v___x_4632_; 
v___x_4627_ = lean_ptr_addr(v_x_4626_);
v___x_4628_ = ((size_t)3ULL);
v___x_4629_ = lean_usize_shift_right(v___x_4627_, v___x_4628_);
v___x_4630_ = lean_usize_to_uint64(v___x_4629_);
v___x_4631_ = lean_uint64_to_usize(v___x_4630_);
v___x_4632_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4625_, v___x_4631_, v_x_4626_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_4633_, lean_object* v_x_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4633_, v_x_4634_);
lean_dec_ref(v_x_4634_);
lean_dec_ref(v_x_4633_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object* v_type_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4639_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4718_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4651_ = v___x_4648_;
v_isShared_4652_ = v_isSharedCheck_4718_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4718_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
uint8_t v_linarith_4653_; 
v_linarith_4653_ = lean_ctor_get_uint8(v_a_4649_, sizeof(void*)*14 + 22);
lean_dec(v_a_4649_);
if (v_linarith_4653_ == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4656_; 
lean_dec_ref(v_type_4636_);
v___x_4654_ = lean_box(0);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4654_);
v___x_4656_ = v___x_4651_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
else
{
lean_object* v___x_4658_; 
lean_del_object(v___x_4651_);
lean_inc_ref(v_type_4636_);
v___x_4658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_4636_, v_a_4639_, v_a_4644_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4709_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4709_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4709_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
uint8_t v___x_4663_; 
v___x_4663_ = lean_unbox(v_a_4659_);
lean_dec(v_a_4659_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; 
lean_del_object(v___x_4661_);
v___x_4664_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_4637_, v_a_4645_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4696_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4696_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4696_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v_typeIdOf_4669_; lean_object* v___x_4670_; 
v_typeIdOf_4669_ = lean_ctor_get(v_a_4665_, 1);
lean_inc_ref(v_typeIdOf_4669_);
lean_dec(v_a_4665_);
v___x_4670_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_typeIdOf_4669_, v_type_4636_);
lean_dec_ref(v_typeIdOf_4669_);
if (lean_obj_tag(v___x_4670_) == 1)
{
lean_object* v_val_4671_; lean_object* v___x_4673_; 
lean_dec_ref(v_type_4636_);
v_val_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_val_4671_);
lean_dec_ref_known(v___x_4670_, 1);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v_val_4671_);
v___x_4673_ = v___x_4667_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_val_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
else
{
lean_object* v___x_4675_; 
lean_dec(v___x_4670_);
lean_del_object(v___x_4667_);
lean_inc_ref(v_type_4636_);
v___x_4675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f(v_type_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc_n(v_a_4676_, 2);
lean_dec_ref_known(v___x_4675_, 1);
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_4677_, 0, v_type_4636_);
lean_closure_set(v___f_4677_, 1, v_a_4676_);
v___x_4678_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4679_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4678_, v___f_4677_, v_a_4637_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; 
v_unused_4687_ = lean_ctor_get(v___x_4679_, 0);
lean_dec(v_unused_4687_);
v___x_4681_ = v___x_4679_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_dec(v___x_4679_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v_a_4676_);
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4676_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_dec(v_a_4676_);
v_a_4688_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4679_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4679_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
else
{
lean_dec_ref(v_type_4636_);
return v___x_4675_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v_type_4636_);
v_a_4697_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4664_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4664_);
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
lean_object* v___x_4705_; lean_object* v___x_4707_; 
lean_dec_ref(v_type_4636_);
v___x_4705_ = lean_box(0);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4705_);
v___x_4707_ = v___x_4661_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
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
lean_dec_ref(v_type_4636_);
v_a_4710_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4658_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4658_);
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
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_dec_ref(v_type_4636_);
v_a_4719_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4648_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4648_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f___boxed(lean_object* v_type_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_type_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec(v_a_4735_);
lean_dec_ref(v_a_4734_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec(v_a_4728_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(lean_object* v_00_u03b2_4740_, lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_x_4741_, v_x_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0(v_00_u03b2_4744_, v_x_4745_, v_x_4746_);
lean_dec_ref(v_x_4746_);
lean_dec_ref(v_x_4745_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_4748_, lean_object* v_x_4749_, size_t v_x_4750_, lean_object* v_x_4751_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___redArg(v_x_4749_, v_x_4750_, v_x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4753_, lean_object* v_x_4754_, lean_object* v_x_4755_, lean_object* v_x_4756_){
_start:
{
size_t v_x_6977__boxed_4757_; lean_object* v_res_4758_; 
v_x_6977__boxed_4757_ = lean_unbox_usize(v_x_4755_);
lean_dec(v_x_4755_);
v_res_4758_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0(v_00_u03b2_4753_, v_x_4754_, v_x_6977__boxed_4757_, v_x_4756_);
lean_dec_ref(v_x_4756_);
lean_dec_ref(v_x_4754_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4759_, lean_object* v_keys_4760_, lean_object* v_vals_4761_, lean_object* v_heq_4762_, lean_object* v_i_4763_, lean_object* v_k_4764_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4760_, v_vals_4761_, v_i_4763_, v_k_4764_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4766_, lean_object* v_keys_4767_, lean_object* v_vals_4768_, lean_object* v_heq_4769_, lean_object* v_i_4770_, lean_object* v_k_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4766_, v_keys_4767_, v_vals_4768_, v_heq_4769_, v_i_4770_, v_k_4771_);
lean_dec_ref(v_k_4771_);
lean_dec_ref(v_vals_4768_);
lean_dec_ref(v_keys_4767_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(lean_object* v_u_4773_, lean_object* v_type_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNoNatZeroDivInst_x3f___redArg___closed__1));
v___x_4782_ = lean_box(0);
v___x_4783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4783_, 0, v_u_4773_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
v___x_4784_ = l_Lean_mkConst(v___x_4781_, v___x_4783_);
v___x_4785_ = l_Lean_Expr_app___override(v___x_4784_, v_type_4774_);
v___x_4786_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4785_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg___boxed(lean_object* v_u_4787_, lean_object* v_type_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4787_, v_type_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
lean_dec(v_a_4791_);
lean_dec_ref(v_a_4790_);
lean_dec(v_a_4789_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(lean_object* v_u_4796_, lean_object* v_type_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_u_4796_, v_type_4797_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___boxed(lean_object* v_u_4810_, lean_object* v_type_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f(v_u_4810_, v_type_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
lean_dec(v_a_4819_);
lean_dec_ref(v_a_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec(v_a_4813_);
lean_dec(v_a_4812_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0(lean_object* v___x_4824_, lean_object* v_s_4825_){
_start:
{
lean_object* v_structs_4826_; lean_object* v_typeIdOf_4827_; lean_object* v_exprToStructId_4828_; lean_object* v_exprToStructIdEntries_4829_; lean_object* v_forbiddenNatModules_4830_; lean_object* v_natStructs_4831_; lean_object* v_natTypeIdOf_4832_; lean_object* v_exprToNatStructId_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4841_; 
v_structs_4826_ = lean_ctor_get(v_s_4825_, 0);
v_typeIdOf_4827_ = lean_ctor_get(v_s_4825_, 1);
v_exprToStructId_4828_ = lean_ctor_get(v_s_4825_, 2);
v_exprToStructIdEntries_4829_ = lean_ctor_get(v_s_4825_, 3);
v_forbiddenNatModules_4830_ = lean_ctor_get(v_s_4825_, 4);
v_natStructs_4831_ = lean_ctor_get(v_s_4825_, 5);
v_natTypeIdOf_4832_ = lean_ctor_get(v_s_4825_, 6);
v_exprToNatStructId_4833_ = lean_ctor_get(v_s_4825_, 7);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_s_4825_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4835_ = v_s_4825_;
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_exprToNatStructId_4833_);
lean_inc(v_natTypeIdOf_4832_);
lean_inc(v_natStructs_4831_);
lean_inc(v_forbiddenNatModules_4830_);
lean_inc(v_exprToStructIdEntries_4829_);
lean_inc(v_exprToStructId_4828_);
lean_inc(v_typeIdOf_4827_);
lean_inc(v_structs_4826_);
lean_dec(v_s_4825_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_array_push(v_natStructs_4831_, v___x_4824_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 5, v___x_4837_);
v___x_4839_ = v___x_4835_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_structs_4826_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v_typeIdOf_4827_);
lean_ctor_set(v_reuseFailAlloc_4840_, 2, v_exprToStructId_4828_);
lean_ctor_set(v_reuseFailAlloc_4840_, 3, v_exprToStructIdEntries_4829_);
lean_ctor_set(v_reuseFailAlloc_4840_, 4, v_forbiddenNatModules_4830_);
lean_ctor_set(v_reuseFailAlloc_4840_, 5, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4840_, 6, v_natTypeIdOf_4832_);
lean_ctor_set(v_reuseFailAlloc_4840_, 7, v_exprToNatStructId_4833_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_ref_4848_; lean_object* v___x_4849_; lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4858_; 
v_ref_4848_ = lean_ctor_get(v___y_4845_, 2);
v___x_4849_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_ensureDefEq_spec__0_spec__0(v_msg_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4852_ = v___x_4849_;
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4849_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4854_; lean_object* v___x_4856_; 
lean_inc(v_ref_4848_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v_ref_4848_);
lean_ctor_set(v___x_4854_, 1, v_a_4850_);
if (v_isShared_4853_ == 0)
{
lean_ctor_set_tag(v___x_4852_, 1);
lean_ctor_set(v___x_4852_, 0, v___x_4854_);
v___x_4856_ = v___x_4852_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4865_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__5);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__6));
v___x_4882_ = l_Lean_stringToMessageData(v___x_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(lean_object* v_type_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v___x_4895_; 
lean_inc_ref(v_type_4883_);
v___x_4895_ = l_Lean_Meta_getDecLevel(v_type_4883_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc_n(v_a_4896_, 2);
lean_dec_ref_known(v___x_4895_, 1);
lean_inc_ref(v_type_4883_);
v___x_4897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_mkNatModuleInst_x3f___redArg(v_a_4896_, v_type_4883_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_5190_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_5190_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_5190_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
if (lean_obj_tag(v_a_4898_) == 1)
{
lean_object* v_val_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_del_object(v___x_4900_);
v_val_4902_ = lean_ctor_get(v_a_4898_, 0);
lean_inc_n(v_val_4902_, 2);
lean_dec_ref_known(v_a_4898_, 1);
v___x_4903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_go_x3f___closed__1));
v___x_4904_ = lean_box(0);
lean_inc(v_a_4896_);
v___x_4905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4905_, 0, v_a_4896_);
lean_ctor_set(v___x_4905_, 1, v___x_4904_);
lean_inc_ref(v___x_4905_);
v___x_4906_ = l_Lean_mkConst(v___x_4903_, v___x_4905_);
lean_inc_ref(v_type_4883_);
v___x_4907_ = l_Lean_mkAppB(v___x_4906_, v_type_4883_, v_val_4902_);
v___x_4908_ = l_Lean_Meta_Sym_canon(v___x_4907_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4910_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
v___x_4910_ = l_Lean_Meta_Sym_shareCommon(v_a_4909_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc_n(v_a_4911_, 2);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(v_a_4911_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
if (lean_obj_tag(v_a_4913_) == 1)
{
lean_object* v_val_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_5165_; 
v_val_4914_ = lean_ctor_get(v_a_4913_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_a_4913_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_4916_ = v_a_4913_;
v_isShared_4917_ = v_isSharedCheck_5165_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_val_4914_);
lean_dec(v_a_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_5165_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__1));
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4919_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4918_, v_a_4896_, v_type_4883_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__3));
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst_x3f___redArg(v___x_4921_, v_a_4896_, v_type_4883_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4922_, 1);
lean_inc(v_a_4920_);
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4924_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_a_4896_, v_type_4883_, v_a_4920_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v_a_4925_; lean_object* v___x_4926_; 
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_a_4925_);
lean_dec_ref_known(v___x_4924_, 1);
lean_inc(v_a_4920_);
lean_inc(v_a_4923_);
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4926_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_a_4896_, v_type_4883_, v_a_4923_, v_a_4920_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4928_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_a_4927_);
lean_dec_ref_known(v___x_4926_, 1);
lean_inc(v_a_4920_);
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4928_ = l_Lean_Meta_Sym_Arith_mkIsLinearOrderInst_x3f(v_a_4896_, v_type_4883_, v_a_4920_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__62));
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4931_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getBinHomoInst___redArg(v___x_4930_, v_a_4896_, v_type_4883_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc_n(v_a_4932_, 2);
lean_dec_ref_known(v___x_4931_, 1);
v___x_4933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__64));
lean_inc_ref(v___x_4905_);
lean_inc_n(v_a_4896_, 2);
v___x_4934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4934_, 0, v_a_4896_);
lean_ctor_set(v___x_4934_, 1, v___x_4905_);
lean_inc_ref(v___x_4934_);
v___x_4935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4935_, 0, v_a_4896_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = l_Lean_mkConst(v___x_4933_, v___x_4935_);
lean_inc_ref_n(v_type_4883_, 3);
v___x_4937_ = l_Lean_mkApp4(v___x_4936_, v_type_4883_, v_type_4883_, v_type_4883_, v_a_4932_);
v___x_4938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4937_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v_orderedAddInst_x3f_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; lean_object* v___y_4950_; lean_object* v___y_4951_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5092_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
if (lean_obj_tag(v_a_4920_) == 1)
{
if (lean_obj_tag(v_a_4925_) == 1)
{
lean_object* v_val_5094_; lean_object* v_val_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; 
v_val_5094_ = lean_ctor_get(v_a_4920_, 0);
v_val_5095_ = lean_ctor_get(v_a_4925_, 0);
v___x_5096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__66));
lean_inc_ref(v___x_4905_);
v___x_5097_ = l_Lean_mkConst(v___x_5096_, v___x_4905_);
lean_inc(v_val_5095_);
lean_inc(v_val_5094_);
lean_inc_ref(v_type_4883_);
v___x_5098_ = l_Lean_mkApp4(v___x_5097_, v_type_4883_, v_a_4932_, v_val_5094_, v_val_5095_);
v___x_5099_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_5098_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5100_);
lean_dec_ref_known(v___x_5099_, 1);
v_orderedAddInst_x3f_4941_ = v_a_5100_;
v___y_4942_ = v_a_4884_;
v___y_4943_ = v_a_4885_;
v___y_4944_ = v_a_4886_;
v___y_4945_ = v_a_4887_;
v___y_4946_ = v_a_4888_;
v___y_4947_ = v_a_4889_;
v___y_4948_ = v_a_4890_;
v___y_4949_ = v_a_4891_;
v___y_4950_ = v_a_4892_;
v___y_4951_ = v_a_4893_;
goto v___jp_4940_;
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec_ref_known(v_a_4925_, 1);
lean_dec_ref_known(v_a_4920_, 1);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4923_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5101_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5099_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5099_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
else
{
lean_dec(v_a_4932_);
v___y_5083_ = v_a_4884_;
v___y_5084_ = v_a_4885_;
v___y_5085_ = v_a_4886_;
v___y_5086_ = v_a_4887_;
v___y_5087_ = v_a_4888_;
v___y_5088_ = v_a_4889_;
v___y_5089_ = v_a_4890_;
v___y_5090_ = v_a_4891_;
v___y_5091_ = v_a_4892_;
v___y_5092_ = v_a_4893_;
goto v___jp_5082_;
}
}
else
{
lean_dec(v_a_4932_);
v___y_5083_ = v_a_4884_;
v___y_5084_ = v_a_4885_;
v___y_5085_ = v_a_4886_;
v___y_5086_ = v_a_4887_;
v___y_5087_ = v_a_4888_;
v___y_5088_ = v_a_4889_;
v___y_5089_ = v_a_4890_;
v___y_5090_ = v_a_4891_;
v___y_5091_ = v_a_4892_;
v___y_5092_ = v_a_4893_;
goto v___jp_5082_;
}
v___jp_4940_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__12));
lean_inc_ref(v___x_4905_);
v___x_4953_ = l_Lean_mkConst(v___x_4952_, v___x_4905_);
lean_inc_ref(v_type_4883_);
v___x_4954_ = l_Lean_Expr_app___override(v___x_4953_, v_type_4883_);
v___x_4955_ = l_Lean_Meta_Sym_synthInstance(v___x_4954_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_a_4956_);
lean_dec_ref_known(v___x_4955_, 1);
v___x_4957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goQ_x3f___closed__14));
lean_inc_ref(v___x_4905_);
v___x_4958_ = l_Lean_mkConst(v___x_4957_, v___x_4905_);
lean_inc_ref(v_type_4883_);
v___x_4959_ = l_Lean_mkAppB(v___x_4958_, v_type_4883_, v_a_4956_);
v___x_4960_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_4959_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__1));
lean_inc_ref(v___x_4905_);
v___x_4963_ = l_Lean_mkConst(v___x_4962_, v___x_4905_);
lean_inc(v_val_4902_);
lean_inc_ref(v_type_4883_);
v___x_4964_ = l_Lean_mkAppB(v___x_4963_, v_type_4883_, v_val_4902_);
v___x_4965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4964_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v___x_4967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__14));
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getInst___redArg(v___x_4967_, v_a_4896_, v_type_4883_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v_a_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v_a_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc(v_a_4969_);
lean_dec_ref_known(v___x_4968_, 1);
v___x_4970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f___closed__16));
v___x_4971_ = l_Lean_mkConst(v___x_4970_, v___x_4905_);
lean_inc_ref(v_type_4883_);
v___x_4972_ = l_Lean_mkAppB(v___x_4971_, v_type_4883_, v_a_4969_);
v___x_4973_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_internalizeConst(v___x_4972_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4975_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
lean_inc_ref(v_type_4883_);
lean_inc(v_a_4896_);
v___x_4975_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulNatInst___redArg(v_a_4896_, v_type_4883_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v___x_4977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntFn_x3f___redArg___closed__1));
v___x_4978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getHSMulIntInst___redArg___closed__2);
v___x_4979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v___x_4934_);
v___x_4980_ = l_Lean_mkConst(v___x_4977_, v___x_4979_);
v___x_4981_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_4883_, 2);
v___x_4982_ = l_Lean_mkApp4(v___x_4980_, v___x_4981_, v_type_4883_, v_type_4883_, v_a_4976_);
v___x_4983_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_preprocess___redArg(v___x_4982_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___x_4983_, 1);
v___x_4985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__4));
lean_inc(v_a_4896_);
v___x_4986_ = l_Lean_Level_succ___override(v_a_4896_);
v___x_4987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v___x_4904_);
v___x_4988_ = l_Lean_mkConst(v___x_4985_, v___x_4987_);
v___x_4989_ = l_Lean_Expr_app___override(v___x_4988_, v_a_4911_);
v___x_4990_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v___y_4942_, v___y_4950_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v_natStructs_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___f_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v_natStructs_4992_ = lean_ctor_get(v_a_4991_, 5);
lean_inc_ref(v_natStructs_4992_);
lean_dec(v_a_4991_);
v___x_4993_ = lean_array_get_size(v_natStructs_4992_);
lean_dec_ref(v_natStructs_4992_);
v___x_4994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__5);
v___x_4995_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4993_);
lean_ctor_set(v___x_4995_, 1, v_val_4914_);
lean_ctor_set(v___x_4995_, 2, v_type_4883_);
lean_ctor_set(v___x_4995_, 3, v_a_4896_);
lean_ctor_set(v___x_4995_, 4, v_val_4902_);
lean_ctor_set(v___x_4995_, 5, v_a_4920_);
lean_ctor_set(v___x_4995_, 6, v_a_4923_);
lean_ctor_set(v___x_4995_, 7, v_a_4927_);
lean_ctor_set(v___x_4995_, 8, v_a_4925_);
lean_ctor_set(v___x_4995_, 9, v_orderedAddInst_x3f_4941_);
lean_ctor_set(v___x_4995_, 10, v_a_4929_);
lean_ctor_set(v___x_4995_, 11, v_a_4961_);
lean_ctor_set(v___x_4995_, 12, v___x_4989_);
lean_ctor_set(v___x_4995_, 13, v_a_4974_);
lean_ctor_set(v___x_4995_, 14, v_a_4966_);
lean_ctor_set(v___x_4995_, 15, v_a_4939_);
lean_ctor_set(v___x_4995_, 16, v_a_4984_);
lean_ctor_set(v___x_4995_, 17, v___x_4994_);
v___f_4996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_4996_, 0, v___x_4995_);
v___x_4997_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4997_, v___f_4996_, v___y_4942_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5008_; 
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5008_ == 0)
{
lean_object* v_unused_5009_; 
v_unused_5009_ = lean_ctor_get(v___x_4998_, 0);
lean_dec(v_unused_5009_);
v___x_5000_ = v___x_4998_;
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
else
{
lean_dec(v___x_4998_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4993_);
v___x_5003_ = v___x_4916_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_4993_);
v___x_5003_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
lean_object* v___x_5005_; 
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 0, v___x_5003_);
v___x_5005_ = v___x_5000_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_del_object(v___x_4916_);
v_a_5010_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4998_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_4998_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec_ref(v___x_4989_);
lean_dec(v_a_4984_);
lean_dec(v_a_4974_);
lean_dec(v_a_4966_);
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5018_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_4990_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_4990_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v_a_4974_);
lean_dec(v_a_4966_);
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5026_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_4983_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_4983_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_a_4974_);
lean_dec(v_a_4966_);
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5034_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_4975_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_4975_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
lean_dec(v_a_4966_);
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5042_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_4973_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_4973_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_a_4966_);
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5050_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_4968_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_4968_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec(v_a_4961_);
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5058_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_4965_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_4965_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5066_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_4960_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_4960_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_dec(v_orderedAddInst_x3f_4941_);
lean_dec(v_a_4939_);
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5074_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_4955_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_4955_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
v___jp_5082_:
{
lean_object* v___x_5093_; 
v___x_5093_ = lean_box(0);
v_orderedAddInst_x3f_4941_ = v___x_5093_;
v___y_4942_ = v___y_5083_;
v___y_4943_ = v___y_5084_;
v___y_4944_ = v___y_5085_;
v___y_4945_ = v___y_5086_;
v___y_4946_ = v___y_5087_;
v___y_4947_ = v___y_5088_;
v___y_4948_ = v___y_5089_;
v___y_4949_ = v___y_5090_;
v___y_4950_ = v___y_5091_;
v___y_4951_ = v___y_5092_;
goto v___jp_4940_;
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref_known(v___x_4934_, 2);
lean_dec(v_a_4932_);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5109_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_4938_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_4938_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5117_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_4931_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_4931_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5120_ == 0)
{
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_dec(v_a_4927_);
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5125_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_4928_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_4928_);
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
lean_dec(v_a_4925_);
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5133_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_4926_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_4926_);
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
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
lean_dec(v_a_4923_);
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5141_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v___x_4924_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_4924_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5146_; 
if (v_isShared_5144_ == 0)
{
v___x_5146_ = v___x_5143_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec(v_a_4920_);
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5149_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_4922_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_4922_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_del_object(v___x_4916_);
lean_dec(v_val_4914_);
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5157_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_4919_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_4919_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
else
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
lean_dec(v_a_4913_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v___x_5166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___closed__7);
v___x_5167_ = l_Lean_indentExpr(v_a_4911_);
v___x_5168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v___x_5168_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_5169_;
}
}
else
{
lean_dec(v_a_4911_);
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
return v___x_4912_;
}
}
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5170_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_4910_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_4910_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec_ref_known(v___x_4905_, 2);
lean_dec(v_val_4902_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5178_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_4908_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_4908_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v___x_5186_; lean_object* v___x_5188_; 
lean_dec(v_a_4898_);
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v___x_5186_ = lean_box(0);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_5186_);
v___x_5188_ = v___x_4900_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
lean_dec(v_a_4896_);
lean_dec_ref(v_type_4883_);
v_a_5191_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_4897_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___x_4897_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_dec_ref(v_type_4883_);
v_a_5199_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_4895_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_4895_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f___boxed(lean_object* v_type_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec(v_a_5211_);
lean_dec_ref(v_a_5210_);
lean_dec(v_a_5209_);
lean_dec(v_a_5208_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_5220_, lean_object* v_msg_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___redArg(v_msg_5221_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_msg_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v_res_5247_; 
v_res_5247_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f_spec__0(v_00_u03b1_5234_, v_msg_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec(v___y_5236_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0(lean_object* v_type_5248_, lean_object* v_a_5249_, lean_object* v_s_5250_){
_start:
{
lean_object* v_structs_5251_; lean_object* v_typeIdOf_5252_; lean_object* v_exprToStructId_5253_; lean_object* v_exprToStructIdEntries_5254_; lean_object* v_forbiddenNatModules_5255_; lean_object* v_natStructs_5256_; lean_object* v_natTypeIdOf_5257_; lean_object* v_exprToNatStructId_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5266_; 
v_structs_5251_ = lean_ctor_get(v_s_5250_, 0);
v_typeIdOf_5252_ = lean_ctor_get(v_s_5250_, 1);
v_exprToStructId_5253_ = lean_ctor_get(v_s_5250_, 2);
v_exprToStructIdEntries_5254_ = lean_ctor_get(v_s_5250_, 3);
v_forbiddenNatModules_5255_ = lean_ctor_get(v_s_5250_, 4);
v_natStructs_5256_ = lean_ctor_get(v_s_5250_, 5);
v_natTypeIdOf_5257_ = lean_ctor_get(v_s_5250_, 6);
v_exprToNatStructId_5258_ = lean_ctor_get(v_s_5250_, 7);
v_isSharedCheck_5266_ = !lean_is_exclusive(v_s_5250_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5260_ = v_s_5250_;
v_isShared_5261_ = v_isSharedCheck_5266_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_exprToNatStructId_5258_);
lean_inc(v_natTypeIdOf_5257_);
lean_inc(v_natStructs_5256_);
lean_inc(v_forbiddenNatModules_5255_);
lean_inc(v_exprToStructIdEntries_5254_);
lean_inc(v_exprToStructId_5253_);
lean_inc(v_typeIdOf_5252_);
lean_inc(v_structs_5251_);
lean_dec(v_s_5250_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5266_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5262_; lean_object* v___x_5264_; 
v___x_5262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getStructId_x3f_goCore_x3f_spec__0___redArg(v_natTypeIdOf_5257_, v_type_5248_, v_a_5249_);
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 6, v___x_5262_);
v___x_5264_ = v___x_5260_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_structs_5251_);
lean_ctor_set(v_reuseFailAlloc_5265_, 1, v_typeIdOf_5252_);
lean_ctor_set(v_reuseFailAlloc_5265_, 2, v_exprToStructId_5253_);
lean_ctor_set(v_reuseFailAlloc_5265_, 3, v_exprToStructIdEntries_5254_);
lean_ctor_set(v_reuseFailAlloc_5265_, 4, v_forbiddenNatModules_5255_);
lean_ctor_set(v_reuseFailAlloc_5265_, 5, v_natStructs_5256_);
lean_ctor_set(v_reuseFailAlloc_5265_, 6, v___x_5262_);
lean_ctor_set(v_reuseFailAlloc_5265_, 7, v_exprToNatStructId_5258_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5267_, lean_object* v_i_5268_, lean_object* v_k_5269_){
_start:
{
lean_object* v___x_5270_; uint8_t v___x_5271_; 
v___x_5270_ = lean_array_get_size(v_keys_5267_);
v___x_5271_ = lean_nat_dec_lt(v_i_5268_, v___x_5270_);
if (v___x_5271_ == 0)
{
lean_dec(v_i_5268_);
return v___x_5271_;
}
else
{
lean_object* v_k_x27_5272_; size_t v___x_5273_; size_t v___x_5274_; uint8_t v___x_5275_; 
v_k_x27_5272_ = lean_array_fget_borrowed(v_keys_5267_, v_i_5268_);
v___x_5273_ = lean_ptr_addr(v_k_5269_);
v___x_5274_ = lean_ptr_addr(v_k_x27_5272_);
v___x_5275_ = lean_usize_dec_eq(v___x_5273_, v___x_5274_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5276_ = lean_unsigned_to_nat(1u);
v___x_5277_ = lean_nat_add(v_i_5268_, v___x_5276_);
lean_dec(v_i_5268_);
v_i_5268_ = v___x_5277_;
goto _start;
}
else
{
lean_dec(v_i_5268_);
return v___x_5271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5279_, lean_object* v_i_5280_, lean_object* v_k_5281_){
_start:
{
uint8_t v_res_5282_; lean_object* v_r_5283_; 
v_res_5282_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5279_, v_i_5280_, v_k_5281_);
lean_dec_ref(v_k_5281_);
lean_dec_ref(v_keys_5279_);
v_r_5283_ = lean_box(v_res_5282_);
return v_r_5283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_5284_, size_t v_x_5285_, lean_object* v_x_5286_){
_start:
{
if (lean_obj_tag(v_x_5284_) == 0)
{
lean_object* v_es_5287_; lean_object* v___x_5288_; size_t v___x_5289_; size_t v___x_5290_; lean_object* v_j_5291_; lean_object* v___x_5292_; 
v_es_5287_ = lean_ctor_get(v_x_5284_, 0);
v___x_5288_ = lean_box(2);
v___x_5289_ = ((size_t)31ULL);
v___x_5290_ = lean_usize_land(v_x_5285_, v___x_5289_);
v_j_5291_ = lean_usize_to_nat(v___x_5290_);
v___x_5292_ = lean_array_get_borrowed(v___x_5288_, v_es_5287_, v_j_5291_);
lean_dec(v_j_5291_);
switch(lean_obj_tag(v___x_5292_))
{
case 0:
{
lean_object* v_key_5293_; size_t v___x_5294_; size_t v___x_5295_; uint8_t v___x_5296_; 
v_key_5293_ = lean_ctor_get(v___x_5292_, 0);
v___x_5294_ = lean_ptr_addr(v_x_5286_);
v___x_5295_ = lean_ptr_addr(v_key_5293_);
v___x_5296_ = lean_usize_dec_eq(v___x_5294_, v___x_5295_);
return v___x_5296_;
}
case 1:
{
lean_object* v_node_5297_; size_t v___x_5298_; size_t v___x_5299_; 
v_node_5297_ = lean_ctor_get(v___x_5292_, 0);
v___x_5298_ = ((size_t)5ULL);
v___x_5299_ = lean_usize_shift_right(v_x_5285_, v___x_5298_);
v_x_5284_ = v_node_5297_;
v_x_5285_ = v___x_5299_;
goto _start;
}
default: 
{
uint8_t v___x_5301_; 
v___x_5301_ = 0;
return v___x_5301_;
}
}
}
else
{
lean_object* v_ks_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; 
v_ks_5302_ = lean_ctor_get(v_x_5284_, 0);
v___x_5303_ = lean_unsigned_to_nat(0u);
v___x_5304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5302_, v___x_5303_, v_x_5286_);
return v___x_5304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5305_, lean_object* v_x_5306_, lean_object* v_x_5307_){
_start:
{
size_t v_x_8678__boxed_5308_; uint8_t v_res_5309_; lean_object* v_r_5310_; 
v_x_8678__boxed_5308_ = lean_unbox_usize(v_x_5306_);
lean_dec(v_x_5306_);
v_res_5309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5305_, v_x_8678__boxed_5308_, v_x_5307_);
lean_dec_ref(v_x_5307_);
lean_dec_ref(v_x_5305_);
v_r_5310_ = lean_box(v_res_5309_);
return v_r_5310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
size_t v___x_5313_; size_t v___x_5314_; size_t v___x_5315_; uint64_t v___x_5316_; size_t v___x_5317_; uint8_t v___x_5318_; 
v___x_5313_ = lean_ptr_addr(v_x_5312_);
v___x_5314_ = ((size_t)3ULL);
v___x_5315_ = lean_usize_shift_right(v___x_5313_, v___x_5314_);
v___x_5316_ = lean_usize_to_uint64(v___x_5315_);
v___x_5317_ = lean_uint64_to_usize(v___x_5316_);
v___x_5318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5311_, v___x_5317_, v_x_5312_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_5319_, lean_object* v_x_5320_){
_start:
{
uint8_t v_res_5321_; lean_object* v_r_5322_; 
v_res_5321_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5319_, v_x_5320_);
lean_dec_ref(v_x_5320_);
lean_dec_ref(v_x_5319_);
v_r_5322_ = lean_box(v_res_5321_);
return v_r_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(lean_object* v_type_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
lean_object* v___x_5335_; 
v___x_5335_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5326_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5425_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5425_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5425_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
uint8_t v_linarith_5340_; 
v_linarith_5340_ = lean_ctor_get_uint8(v_a_5336_, sizeof(void*)*14 + 22);
lean_dec(v_a_5336_);
if (v_linarith_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5343_; 
lean_dec_ref(v_type_5323_);
v___x_5341_ = lean_box(0);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5341_);
v___x_5343_ = v___x_5338_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5341_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
else
{
lean_object* v___x_5345_; 
lean_del_object(v___x_5338_);
v___x_5345_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5324_, v_a_5332_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5416_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5348_ = v___x_5345_;
v_isShared_5349_ = v_isSharedCheck_5416_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5345_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5416_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v_forbiddenNatModules_5350_; uint8_t v___x_5351_; 
v_forbiddenNatModules_5350_ = lean_ctor_get(v_a_5346_, 4);
lean_inc_ref(v_forbiddenNatModules_5350_);
lean_dec(v_a_5346_);
v___x_5351_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_forbiddenNatModules_5350_, v_type_5323_);
lean_dec_ref(v_forbiddenNatModules_5350_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
lean_del_object(v___x_5348_);
lean_inc_ref(v_type_5323_);
v___x_5352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_isCutsatType___redArg(v_type_5323_, v_a_5326_, v_a_5331_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5403_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5403_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5403_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
uint8_t v___x_5357_; 
v___x_5357_ = lean_unbox(v_a_5353_);
lean_dec(v_a_5353_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
lean_del_object(v___x_5355_);
v___x_5358_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_5324_, v_a_5332_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5390_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5361_ = v___x_5358_;
v_isShared_5362_ = v_isSharedCheck_5390_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5390_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_natTypeIdOf_5363_; lean_object* v___x_5364_; 
v_natTypeIdOf_5363_ = lean_ctor_get(v_a_5359_, 6);
lean_inc_ref(v_natTypeIdOf_5363_);
lean_dec(v_a_5359_);
v___x_5364_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getStructId_x3f_spec__0___redArg(v_natTypeIdOf_5363_, v_type_5323_);
lean_dec_ref(v_natTypeIdOf_5363_);
if (lean_obj_tag(v___x_5364_) == 1)
{
lean_object* v_val_5365_; lean_object* v___x_5367_; 
lean_dec_ref(v_type_5323_);
v_val_5365_ = lean_ctor_get(v___x_5364_, 0);
lean_inc(v_val_5365_);
lean_dec_ref_known(v___x_5364_, 1);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v_val_5365_);
v___x_5367_ = v___x_5361_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_val_5365_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
else
{
lean_object* v___x_5369_; 
lean_dec(v___x_5364_);
lean_del_object(v___x_5361_);
lean_inc_ref(v_type_5323_);
v___x_5369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_StructId_0__Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_go_x3f(v_type_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v_a_5370_; lean_object* v___f_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
lean_inc_n(v_a_5370_, 2);
lean_dec_ref_known(v___x_5369_, 1);
v___f_5371_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_5371_, 0, v_type_5323_);
lean_closure_set(v___f_5371_, 1, v_a_5370_);
v___x_5372_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5373_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5372_, v___f_5371_, v_a_5324_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5380_ == 0)
{
lean_object* v_unused_5381_; 
v_unused_5381_ = lean_ctor_get(v___x_5373_, 0);
lean_dec(v_unused_5381_);
v___x_5375_ = v___x_5373_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_dec(v___x_5373_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v_a_5370_);
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5370_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec(v_a_5370_);
v_a_5382_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5373_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5373_);
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
lean_dec_ref(v_type_5323_);
return v___x_5369_;
}
}
}
}
else
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5398_; 
lean_dec_ref(v_type_5323_);
v_a_5391_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5393_ = v___x_5358_;
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5358_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5396_; 
if (v_isShared_5394_ == 0)
{
v___x_5396_ = v___x_5393_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
lean_dec_ref(v_type_5323_);
v___x_5399_ = lean_box(0);
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 0, v___x_5399_);
v___x_5401_ = v___x_5355_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec_ref(v_type_5323_);
v_a_5404_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5352_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5352_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
else
{
lean_object* v___x_5412_; lean_object* v___x_5414_; 
lean_dec_ref(v_type_5323_);
v___x_5412_ = lean_box(0);
if (v_isShared_5349_ == 0)
{
lean_ctor_set(v___x_5348_, 0, v___x_5412_);
v___x_5414_ = v___x_5348_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5412_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
lean_dec_ref(v_type_5323_);
v_a_5417_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5345_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5345_);
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
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
lean_dec_ref(v_type_5323_);
v_a_5426_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5335_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5335_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f___boxed(lean_object* v_type_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f(v_type_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
lean_dec(v_a_5444_);
lean_dec_ref(v_a_5443_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec_ref(v_a_5439_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec(v_a_5435_);
return v_res_5446_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(lean_object* v_00_u03b2_5447_, lean_object* v_x_5448_, lean_object* v_x_5449_){
_start:
{
uint8_t v___x_5450_; 
v___x_5450_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___redArg(v_x_5448_, v_x_5449_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_5451_, lean_object* v_x_5452_, lean_object* v_x_5453_){
_start:
{
uint8_t v_res_5454_; lean_object* v_r_5455_; 
v_res_5454_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0(v_00_u03b2_5451_, v_x_5452_, v_x_5453_);
lean_dec_ref(v_x_5453_);
lean_dec_ref(v_x_5452_);
v_r_5455_ = lean_box(v_res_5454_);
return v_r_5455_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5456_, lean_object* v_x_5457_, size_t v_x_5458_, lean_object* v_x_5459_){
_start:
{
uint8_t v___x_5460_; 
v___x_5460_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___redArg(v_x_5457_, v_x_5458_, v_x_5459_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5461_, lean_object* v_x_5462_, lean_object* v_x_5463_, lean_object* v_x_5464_){
_start:
{
size_t v_x_8946__boxed_5465_; uint8_t v_res_5466_; lean_object* v_r_5467_; 
v_x_8946__boxed_5465_ = lean_unbox_usize(v_x_5463_);
lean_dec(v_x_5463_);
v_res_5466_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0(v_00_u03b2_5461_, v_x_5462_, v_x_8946__boxed_5465_, v_x_5464_);
lean_dec_ref(v_x_5464_);
lean_dec_ref(v_x_5462_);
v_r_5467_ = lean_box(v_res_5466_);
return v_r_5467_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5468_, lean_object* v_keys_5469_, lean_object* v_vals_5470_, lean_object* v_heq_5471_, lean_object* v_i_5472_, lean_object* v_k_5473_){
_start:
{
uint8_t v___x_5474_; 
v___x_5474_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5469_, v_i_5472_, v_k_5473_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5475_, lean_object* v_keys_5476_, lean_object* v_vals_5477_, lean_object* v_heq_5478_, lean_object* v_i_5479_, lean_object* v_k_5480_){
_start:
{
uint8_t v_res_5481_; lean_object* v_r_5482_; 
v_res_5481_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Linear_getNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5475_, v_keys_5476_, v_vals_5477_, v_heq_5478_, v_i_5479_, v_k_5480_);
lean_dec_ref(v_k_5480_);
lean_dec_ref(v_vals_5477_);
lean_dec_ref(v_keys_5476_);
v_r_5482_ = lean_box(v_res_5481_);
return v_r_5482_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
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
